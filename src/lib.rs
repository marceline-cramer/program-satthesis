use std::{collections::BTreeMap, fmt::Display};

use im::{HashSet, OrdSet};
use satisfaction::{
    cadical::CadicalBackend,
    expr::{BoolExpr, Clause, Literal},
    SatResult, Scope, Solver,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Variable {
    Base(i32),
    NonDeterministic(i32),
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Variable::Base(var) => write!(f, "{var}"),
            Variable::NonDeterministic(var) => write!(f, "{var}-nondet"),
        }
    }
}

pub fn infer_variables(clauses: OrdSet<Clause<i32>>) -> InferenceMap {
    let mut var_map = BTreeMap::new();

    for clause in clauses {
        for (idx, lit) in clause.iter().enumerate() {
            let clause: Clause<_> = clause
                .iter()
                .enumerate()
                .filter(|(src, _lit)| *src != idx)
                .map(|(_src, lit)| lit.negate())
                // TODO: Literal::map() in upstream satisfaction
                .map(|lit| Literal {
                    variable: Variable::Base(lit.variable),
                    polarity: lit.polarity,
                })
                .collect();

            let vars = clause.iter().map(|lit| lit.variable).collect();

            let body = HornBody { clause, vars };

            let var: &mut VariableInference = var_map.entry(lit.variable).or_default();

            if lit.polarity {
                var.positive.insert(body);
            } else {
                var.negative.insert(body);
            }
        }
    }

    var_map
}

pub type InferenceMap = BTreeMap<i32, VariableInference>;

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

    pub fn polarity_expr(&self, pol: bool) -> BoolExpr<Variable> {
        let bodies = if pol { &self.positive } else { &self.negative };

        let clauses = bodies
            .iter()
            .map(|body| BoolExpr::And(body.clause.iter().cloned().map(BoolExpr::from).collect()))
            .collect();

        BoolExpr::Or(clauses)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HornBody {
    pub clause: Clause<Variable>,
    pub vars: HashSet<Variable>,
}

pub type SearchScope = Scope<Variable, CadicalBackend<CadicalCallbacks>>;

pub struct CadicalCallbacks;

impl cadical::Callbacks for CadicalCallbacks {}

pub struct SearchNode {
    pub scope: SearchScope,
    pub assigned: HashSet<Variable>,
    pub children: Vec<i32>,
    pub inference: InferenceMap,
    pub inferred: InferenceMap,
    pub log: String,
    pub nondet_num: usize,
}

impl SearchNode {
    pub fn new(scope: SearchScope, vars: InferenceMap) -> Self {
        let mut root = Self {
            scope,
            assigned: HashSet::default(),
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

    /// Assigns a variable.
    pub fn assign(&mut self, var: i32) {
        // retrieve the active inferences for this variable
        let infer = self.inferred.remove(&var).unwrap_or_default();

        // track this variable
        self.assigned.insert(Variable::Base(var));

        // constrain the value of the variable based on inference
        if infer.is_empty() {
            // there are no clauses constraining this variable, so it is non-deterministic
            self.nondet_num += 1;
            self.log.push_str(&format!("{var} = nondet()\n"));
        } else {
            // there are clauses constraining the variable, so get their expressions
            let positive_def = infer.polarity_expr(true);
            let negative_def = infer.polarity_expr(false);

            // find the condition that the variable is constrained to
            let condition = if !infer.has_negative() {
                // the variable is unconstrained by negative clauses; use positive
                positive_def
            } else if !infer.has_positive() {
                // the variable is unconstrained by positive clauses; use negative
                negative_def.not()
            } else {
                // find out if the program permits neither polarity's inference
                let neither = positive_def.or(&negative_def).not();
                let allows_neither = self.scope.push().assert(neither).check() == SatResult::Sat;

                // if it does, we need to add a non-deterministic case to cover all solutions
                let nondet = if allows_neither {
                    self.nondet_num += 1;
                    BoolExpr::Variable(Variable::NonDeterministic(var))
                } else {
                    // TODO: BoolExpr::True?
                    BoolExpr::Or(Default::default())
                };

                // either positive or negative can be inferred, so acknowledge
                // inference while allowing for non-determinism
                let negative = negative_def.not().and(&nondet);
                positive_def.or(&negative)
            };

            // constrain the value of the variable
            self.log.push_str(&format!("{var} = {condition}\n"));
            let var = BoolExpr::Variable(Variable::Base(var));
            self.scope.assert(var.iff(&condition));
        }
    }

    /// Finds one possible child of this search subtree, if there is one.
    pub fn search(&mut self, found_solution: &mut bool) -> Option<Self> {
        // abort if the search is complete
        if self.unassigned().is_empty() {
            assert!(self.check_validity());
            *found_solution = true;
            return None;
        }

        // find a valid child
        while let Some(var) = self.children.pop() {
            // set up the child
            let mut child = Self {
                scope: self.scope.push(),
                assigned: self.assigned.clone(),
                children: self.children.clone(),
                inference: self.inference.clone(),
                inferred: self.inferred.clone(),
                log: self.log.clone(),
                nondet_num: self.nondet_num,
            };

            // assign the variable and infer remaining clauses
            child.assign(var);
            child.infer_clauses();

            // verify the child's validity
            if !child.check_validity() {
                // if the child is invalid, try another one
                let depth = self.assigned.len();
                let msg = format!("conflict at depth {depth:<4} in variable {var}\n");
                self.log.push_str(&msg);
                continue;
            }

            // populate the child's children and return it
            child.populate_children();
            return Some(child);
        }

        // no child could be found
        println!("failed to descend:\n{}", self.log);
        None
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
                if infer.is_empty() && !self.assigned.contains(&Variable::Base(*var)) {
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
    pub fn unassigned(&self) -> HashSet<i32> {
        self.inference
            .keys()
            .filter(|var| !self.assigned.contains(&Variable::Base(**var)))
            .copied()
            .collect()
    }

    /// Checks if the current problem is satisfiable.
    pub fn check_validity(&self) -> bool {
        self.scope.check() == SatResult::Sat
    }
}

pub fn run(path: &str, silent: bool) {
    let src = std::fs::read_to_string(path).unwrap();
    let base_clauses = satisfaction::read_dimacs(&src);

    let backend = CadicalBackend::default();
    let solver = Solver::new(backend);
    let mut scope = Scope::new(solver);

    for clause in base_clauses.iter() {
        let terms = clause
            .iter()
            .copied()
            .map(|lit| {
                let var = BoolExpr::Variable(Variable::Base(lit.variable));
                if lit.polarity {
                    var
                } else {
                    var.not()
                }
            })
            .collect();

        let clause = BoolExpr::Or(terms);
        scope.assert(clause);
    }

    assert_eq!(scope.check(), SatResult::Sat);

    let inferred = infer_variables(base_clauses);
    let base = SearchNode::new(scope.push(), inferred);
    let mut stack = vec![base];
    let mut deepest = 0;
    let mut found_solution = false;
    while let Some(node) = stack.last_mut() {
        match node.search(&mut found_solution) {
            Some(child) => {
                if !silent && child.assigned.len() > deepest {
                    deepest = child.assigned.len();
                    println!("new deepest: {deepest}");
                    println!("non-deterministic variables: {}", child.nondet_num);
                }

                stack.push(child);
            }
            None => {
                if found_solution {
                    if !silent {
                        println!("solution found:",);
                        println!("{}", node.log);
                        println!("{} non-deterministic variables.", node.nondet_num);
                    }

                    break;
                }

                stack.pop();
            }
        }
    }
}
