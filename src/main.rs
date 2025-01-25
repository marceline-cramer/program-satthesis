use std::{
    collections::{BTreeMap, HashSet},
    path::Path,
    sync::Arc,
};

use z3::{
    ast::{Ast, Bool},
    Config, Context, SatResult, Solver,
};

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
                var.positive.push(body);
            } else {
                var.negative.push(body);
            }
        }
    }

    var_map
}

#[derive(Debug, Default)]
pub struct VariableInference {
    pub positive: Vec<HornBody>,
    pub negative: Vec<HornBody>,
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

    pub fn only_assigned(&self, assigned: &HashSet<Variable>) -> Self {
        Self {
            positive: self
                .positive
                .iter()
                .filter(|body| body.vars.is_subset(assigned))
                .cloned()
                .collect(),
            negative: self
                .negative
                .iter()
                .filter(|body| body.vars.is_subset(assigned))
                .cloned()
                .collect(),
        }
    }

    pub fn polarity_ast<'ctx>(
        &self,
        ctx: &'ctx Context,
        values: &BTreeMap<Variable, Bool<'ctx>>,
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

    pub fn print(&self, var: Variable) {
        println!("{var} positive:");
        for body in self.positive.iter() {
            println!("\t{}", format_clause(&body.clause));
        }

        println!("{var} negative:");
        for body in self.negative.iter() {
            println!("\t{}", format_clause(&body.clause));
        }
    }
}

#[derive(Clone, Debug)]
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
    pub values: BTreeMap<Variable, Bool<'ctx>>,
    pub remaining_vars: Vec<Variable>,
    pub remaining_idx: usize,
    pub variable_inference: Arc<BTreeMap<Variable, VariableInference>>,
    pub log: String,
    pub nondet_num: usize,
}

impl<'ctx> SearchNode<'ctx> {
    pub fn new(
        ctx: &'ctx Context,
        solver: &'ctx Solver<'ctx>,
        variable_inference: BTreeMap<Variable, VariableInference>,
    ) -> Self {
        Self {
            ctx,
            solver,
            assigned: HashSet::new(),
            values: BTreeMap::new(),
            remaining_vars: variable_inference.keys().copied().collect(),
            remaining_idx: 0,
            variable_inference: Arc::new(variable_inference),
            log: String::new(),
            nondet_num: 0,
        }
    }

    pub fn prioritize_remaining(&mut self) {
        self.remaining_vars.sort_by_cached_key(|var| {
            let infer = self
                .variable_inference
                .get(var)
                .unwrap()
                .only_assigned(&self.assigned);

            let product = (infer.positive.len() * infer.negative.len()) as isize;
            let sum = (infer.positive.len() + infer.negative.len()) as isize;
            (-product, sum)
        });
    }

    pub fn search(&mut self) -> Option<Self> {
        if self.remaining_vars.is_empty() {
            println!(
                "solution found with {} non-deterministic variables:",
                self.nondet_num
            );
            println!("{}", self.log);
            assert!(self.solver.check() == SatResult::Sat);
            panic!();
            self.solver.pop(1);
            return None;
        }

        if self.remaining_idx >= self.remaining_vars.len() {
            return None;
        }

        let mut child = self.clone();
        let var = child.remaining_vars.remove(self.remaining_idx);
        self.remaining_idx += 1;
        child.remaining_idx = 0;

        let infer = self
            .variable_inference
            .get(&var)
            .unwrap()
            .only_assigned(&self.assigned);

        child.solver.push();
        let val = Bool::new_const(self.ctx, format!("{var}"));
        child.values.insert(var, val.clone());
        if infer.is_empty() {
            child.nondet_num += 1;
            child.log.push_str(&format!("{var} = nondet()\n"));
        } else {
            let positive_def = infer.polarity_ast(self.ctx, &self.values, true);
            let negative_def = infer.polarity_ast(self.ctx, &self.values, false);

            let condition = if !infer.has_negative() {
                positive_def
            } else if !infer.has_positive() {
                negative_def.not()
            } else {
                let conflict = Bool::and(self.ctx, &[&positive_def, &negative_def]);
                self.solver.assert(&conflict.not());

                let neither = Bool::or(self.ctx, &[&positive_def, &negative_def]);
                let nondet = if self.solver.check_assumptions(&[neither.not()]) == SatResult::Sat {
                    child.nondet_num += 1;
                    Bool::new_const(self.ctx, format!("{var}-nondet"))
                } else {
                    Bool::from_bool(self.ctx, true)
                };

                if infer.positive.len() > infer.negative.len() {
                    let positive = Bool::or(self.ctx, &[&positive_def, &nondet]);
                    Bool::and(self.ctx, &[&negative_def.not(), &positive])
                } else {
                    let negative = Bool::and(self.ctx, &[&negative_def.not(), &nondet]);
                    Bool::or(self.ctx, &[&positive_def, &negative])
                }
            };

            let condition = condition.simplify();
            child.log.push_str(&format!("{var} = {condition}\n"));
            self.solver.assert(&val.iff(&condition));
        }

        if self.solver.check() != SatResult::Sat {
            println!("conflict in {var}:");
            println!("{}", self.log);
            self.solver.pop(1);
            return None;
        }

        child.assigned.insert(var);
        child.prioritize_remaining();
        Some(child)
    }
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("expected path to DIMACS file");

    let base_clauses = read_dimacs(&path);
    let inferred = infer_variables(base_clauses);

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let base = SearchNode::new(&ctx, &solver, inferred);

    let mut stack = vec![base];
    while let Some(node) = stack.last_mut() {
        match node.search() {
            Some(child) => stack.push(child),
            None => {
                stack.pop();
            }
        }
    }
}
