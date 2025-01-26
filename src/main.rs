use std::{collections::BTreeMap, path::Path, sync::Arc};

use im::{HashMap, HashSet};
use z3::{ast::Bool, Config, Context, SatResult, Solver};

pub fn read_dimacs(path: impl AsRef<Path>) -> Vec<Clause> {
    let src = std::fs::read_to_string(path).expect("failed to read DIMACS file");

    let mut words = src
        .lines()
        .filter(|line| !line.starts_with('c'))
        .flat_map(|line| line.split_whitespace());

    assert_eq!(words.next(), Some("p"));
    assert_eq!(words.next(), Some("cnf"));

    let _var_num: usize = words
        .next()
        .expect("expected variable count")
        .parse()
        .expect("failed to parse variable count");

    let clause_num = words
        .next()
        .expect("expected clause count")
        .parse()
        .expect("failed to parse clause count");

    let mut clauses = Vec::with_capacity(clause_num);
    let mut clause = Vec::new();

    for word in words {
        if let Some(var) = word.strip_prefix('-') {
            let var = var.parse().expect("failed to parse variable");
            clause.push(Literal { var, pol: false });
        } else if word == "%" {
            break;
        } else if word == "0" {
            clause.sort();
            clauses.push(std::mem::take(&mut clause).into());
        } else {
            let var = word.parse().expect("failed to parse variable");
            clause.push(Literal { var, pol: true });
        }
    }

    clauses
}

pub fn infer_variables(clauses: Vec<Clause>) -> BTreeMap<Variable, VariableInference> {
    let mut var_map = BTreeMap::new();

    for clause in clauses {
        for (idx, lit) in clause.iter().enumerate() {
            let clause: Clause = clause
                .iter()
                .enumerate()
                .filter(|(src, _lit)| *src != idx)
                .map(|(_src, lit)| lit.negate())
                .collect();

            let vars = clause.iter().map(|lit| lit.var).collect();

            let body = HornBody { clause, vars };

            let var: &mut VariableInference = var_map.entry(lit.var).or_default();

            if lit.pol {
                var.positive.insert(body);
            } else {
                var.negative.insert(body);
            }
        }
    }

    var_map
}

pub type InferenceMap = BTreeMap<Variable, VariableInference>;

#[derive(Clone, Debug, Default)]
pub struct VariableInference {
    pub positive: HashSet<HornBody>,
    pub negative: HashSet<HornBody>,
}

impl VariableInference {
    pub fn is_empty(&self) -> bool {
        self.positive.is_empty() && self.negative.is_empty()
    }

    pub fn has_negative(&self) -> bool {
        !self.negative.is_empty()
    }

    pub fn has_positive(&self) -> bool {
        !self.positive.is_empty()
    }

    pub fn take_fully_assigned(&mut self, dst: &mut Self, assigned: &HashSet<Variable>) {
        self.positive.retain(|body| {
            if body.vars.is_subset(assigned) {
                dst.positive.insert(body.clone());
                false
            } else {
                true
            }
        });

        self.negative.retain(|body| {
            if body.vars.is_subset(assigned) {
                dst.negative.insert(body.clone());
                false
            } else {
                true
            }
        });
    }

    pub fn polarity_ast<'ctx>(
        &self,
        ctx: &'ctx Context,
        values: &HashMap<Variable, Bool<'ctx>>,
        pol: bool,
    ) -> Bool<'ctx> {
        let bodies = if pol { &self.positive } else { &self.negative };

        let clauses: Vec<_> = bodies
            .iter()
            .map(|body| {
                let clause: Vec<_> = body
                    .clause
                    .iter()
                    .map(|lit| {
                        let value = values.get(&lit.var).unwrap();
                        if lit.pol {
                            value.clone()
                        } else {
                            value.not()
                        }
                    })
                    .collect();

                let clause: Vec<_> = clause.iter().collect();
                Bool::and(ctx, &clause)
            })
            .collect();

        let clauses: Vec<_> = clauses.iter().collect();
        Bool::or(ctx, &clauses)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HornBody {
    pub clause: Clause,
    pub vars: HashSet<Variable>,
}

pub type Clause = Arc<[Literal]>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    pub var: Variable,
    pub pol: bool,
}

impl Literal {
    pub fn negate(self) -> Self {
        Self {
            var: self.var,
            pol: !self.pol,
        }
    }
}

pub type Variable = u16;

pub fn format_clause(clause: &Clause) -> String {
    clause
        .iter()
        .map(|lit| {
            if lit.pol {
                format!("{}", lit.var)
            } else {
                format!("-{}", lit.var)
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

#[derive(Clone, Debug)]
pub struct SearchNode<'ctx> {
    pub ctx: &'ctx Context,
    pub solver: &'ctx Solver<'ctx>,
    pub assigned: HashSet<Variable>,
    pub values: HashMap<Variable, Bool<'ctx>>,
    pub children: Vec<Variable>,
    pub inference: InferenceMap,
    pub inferred: InferenceMap,
    pub log: String,
    pub nondet_num: usize,
}

impl<'ctx> SearchNode<'ctx> {
    pub fn new(ctx: &'ctx Context, solver: &'ctx Solver<'ctx>, vars: InferenceMap) -> Self {
        let mut root = Self {
            ctx,
            solver,
            assigned: HashSet::default(),
            values: HashMap::default(),
            children: vec![],
            inference: vars.clone(),
            inferred: InferenceMap::default(),
            log: String::new(),
            nondet_num: 0,
        };

        root.populate_children();

        root
    }

    /// Populates the children field with a prioritized list of variables.
    pub fn populate_children(&mut self) {
        // find the list of unassigned variables
        self.children = self.unassigned().into_iter().collect();

        // sort them by their priority
        self.children.sort_by_cached_key(|var| {
            let infer = self.inference.get(var).cloned().unwrap_or_default();
            let product1 = (infer.positive.len() * infer.negative.len()) as isize;
            let inferred = self.inferred.get(var).cloned().unwrap_or_default();
            let product2 = ((inferred.positive.len() + 1) * (inferred.negative.len() + 1)) as isize;
            (-product1, product2)
        });
    }

    /// Converts a clause into a Z3 AST using assigned variables.
    pub fn clause_to_ast(&self, clause: &Clause) -> Bool<'ctx> {
        let clause: Vec<_> = clause
            .iter()
            .map(|lit| {
                let value = self.values.get(&lit.var).unwrap();
                if lit.pol {
                    value.clone()
                } else {
                    value.not()
                }
            })
            .collect();

        let clause: Vec<_> = clause.iter().collect();
        Bool::and(self.ctx, &clause)
    }

    /// Adds assertions to guarantee that clauses are not violated by assigned variables.
    ///
    /// As a side-effect, immediately assigns variables who have no remaining clauses.
    pub fn infer_clauses(&mut self) {
        // iteratively propagate all clause inferences
        loop {
            // keep track of new variables that should be immediately assigned
            let mut immediately_assign = Vec::new();

            // find all of the new variable inferences from the currently assigned variables
            for (var, infer) in self.inference.iter_mut() {
                let dst = self.inferred.entry(*var).or_default();
                infer.take_fully_assigned(dst, &self.assigned);

                // if a variable's inference has been depleted, assign it ASAP
                if infer.is_empty() && !self.assigned.contains(var) {
                    immediately_assign.push(*var);
                }
            }

            // if no variables need to be immediately assigned, break the loop
            if immediately_assign.is_empty() {
                break;
            }

            // assign all of the following variables
            for var in immediately_assign {
                self.log.push_str(&format!("immediately assigning {var}\n"));
                self.assign(var);
            }
        }
    }

    /// Find the set of variables that have not been assigned yet.
    pub fn unassigned(&self) -> HashSet<Variable> {
        self.inference
            .keys()
            .filter(|var| !self.assigned.contains(var))
            .copied()
            .collect()
    }

    /// Assigns a variable.
    pub fn assign(&mut self, var: Variable) {
        // retrieve the active inferences for this variable
        let infer = self.inferred.remove(&var).unwrap_or_default();

        // create an AST variable to represent this variable
        let val = Bool::new_const(self.ctx, format!("{var}"));

        // track this variable
        self.assigned.insert(var);
        self.values.insert(var, val.clone());

        // constrain the value of the variable based on inference
        if infer.is_empty() {
            // there are no clauses constraining this variable, so it is non-deterministic
            self.nondet_num += 1;
            self.log.push_str(&format!("{var} = nondet()\n"));
        } else {
            // there are clauses constraining the variable, so get their ASTs
            let positive_def = infer.polarity_ast(self.ctx, &self.values, true);
            let negative_def = infer.polarity_ast(self.ctx, &self.values, false);

            // find the condition that the variable is constrained to
            let condition = if !infer.has_negative() {
                // the variable is unconstrained by negative clauses; use positive
                positive_def
            } else if !infer.has_positive() {
                // the variable is unconstrained by positive clauses; use negative
                negative_def.not()
            } else {
                // find out if the program permits neither polarity's inference
                let neither = Bool::or(self.ctx, &[&positive_def, &negative_def]).not();
                let allows_neither = self.solver.check_assumptions(&[neither]) == SatResult::Sat;

                // if it does, we need to add a non-deterministic case to cover all solutions
                let nondet = if allows_neither {
                    self.nondet_num += 1;
                    Bool::new_const(self.ctx, format!("{var}-nondet"))
                } else {
                    Bool::from_bool(self.ctx, true)
                };

                // either positive or negative can be inferred, so acknowledge
                // inference while allowing for non-determinism
                let negative = Bool::and(self.ctx, &[&negative_def.not(), &nondet]);
                Bool::or(self.ctx, &[&positive_def, &negative])
            };

            // constrain the value of the variable
            self.log.push_str(&format!("{var} = {condition}\n"));
            self.solver.assert(&val.iff(&condition));
        }
    }

    /// Checks if the current problem is satisfiable.
    pub fn check_validity(&self) -> bool {
        self.solver.check() == SatResult::Sat
    }

    /// Finds one possible child of this search subtree, if there is one.
    pub fn search(&mut self) -> Option<Self> {
        // abort if the search is complete
        if self.unassigned().is_empty() {
            println!("solution found:",);
            println!("{}", self.solver);
            println!("{}", self.log);
            println!("{} non-deterministic variables.", self.nondet_num);
            assert!(self.solver.check() == SatResult::Sat);
            panic!();
            self.solver.pop(1);
            return None;
        }

        // find a valid child
        while let Some(var) = self.children.pop() {
            // enter a Z3 scope
            self.solver.push();

            // set up the child
            let mut child = self.clone();
            child.assign(var);
            child.infer_clauses();

            // verify the child's validity
            if !child.check_validity() {
                // if the child is invalid, try another one
                let depth = self.assigned.len();
                println!("conflict in {depth:<4} at {var}");
                self.solver.pop(1);
                continue;
            }

            // populate the child's children and return it
            child.populate_children();
            return Some(child);
        }

        // no child could be found
        self.solver.pop(1);
        None
    }
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("expected path to DIMACS file");

    let base_clauses = read_dimacs(&path);

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    for clause in base_clauses.iter() {
        let terms: Vec<_> = clause
            .iter()
            .map(|lit| {
                let var = Bool::new_const(&ctx, format!("{}", lit.var));
                if lit.pol {
                    var
                } else {
                    var.not()
                }
            })
            .collect();

        let terms: Vec<_> = terms.iter().collect();
        let clause = Bool::or(&ctx, &terms);
        solver.assert(&clause);
    }

    let inferred = infer_variables(base_clauses);
    let base = SearchNode::new(&ctx, &solver, inferred);
    let mut stack = vec![base];
    let mut deepest = 0;
    while let Some(node) = stack.last_mut() {
        match node.search() {
            Some(child) => {
                if child.assigned.len() > deepest {
                    deepest = child.assigned.len();
                    println!("new deepest: {deepest}");
                    println!("non-deterministic variables: {}", child.nondet_num);
                }

                stack.push(child);
            }
            None => {
                stack.pop();
            }
        }
    }
}
