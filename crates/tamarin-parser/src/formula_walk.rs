//! Iterative operations on surface formulas and proof trees.

use crate::ast::{Formula, ParsedMethod, ParsedProofTree};

impl Formula {
    #[inline]
    fn has_children(&self) -> bool {
        !matches!(self, Self::False | Self::True | Self::Atom(_))
    }

    #[inline]
    pub(crate) fn children(&self) -> impl DoubleEndedIterator<Item = &Self> {
        let children = match self {
            Self::Not(a) | Self::Forall(_, a) | Self::Exists(_, a) => [Some(a.as_ref()), None],
            Self::And(a, b) | Self::Or(a, b) | Self::Implies(a, b) | Self::Iff(a, b) => {
                [Some(a.as_ref()), Some(b.as_ref())]
            }
            Self::False | Self::True | Self::Atom(_) => [None, None],
        };
        children.into_iter().flatten()
    }

    #[inline]
    fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Self> {
        let children = match self {
            Self::Not(a) | Self::Forall(_, a) | Self::Exists(_, a) => [Some(a.as_mut()), None],
            Self::And(a, b) | Self::Or(a, b) | Self::Implies(a, b) | Self::Iff(a, b) => {
                [Some(a.as_mut()), Some(b.as_mut())]
            }
            Self::False | Self::True | Self::Atom(_) => [None, None],
        };
        children.into_iter().flatten()
    }

    pub(crate) fn visit(&self, mut visit: impl FnMut(&Self)) {
        let mut pending = Vec::new();
        let mut next = Some(self);
        while let Some(formula) = next.take().or_else(|| pending.pop()) {
            visit(formula);
            for child in formula.children().rev() {
                if let Some(previous) = next.replace(child) {
                    pending.push(previous);
                }
            }
        }
    }

    /// Visit in preorder; false skips children, for example below a shadowing binder.
    pub(crate) fn visit_mut(&mut self, mut visit: impl FnMut(&mut Self) -> bool) {
        let mut pending = Vec::new();
        let mut next = Some(self);
        while let Some(formula) = next.take().or_else(|| pending.pop()) {
            if !visit(formula) {
                continue;
            }
            for child in formula.children_mut().rev() {
                if let Some(previous) = next.replace(child) {
                    pending.push(previous);
                }
            }
        }
    }

    #[inline]
    fn copy_shallow(&self) -> Self {
        match self {
            Self::False => Self::False,
            Self::True => Self::True,
            Self::Atom(a) => Self::Atom(a.clone()),
            Self::Not(_) => Self::Not(Box::new(Self::False)),
            Self::And(_, _) => Self::And(Box::new(Self::False), Box::new(Self::False)),
            Self::Or(_, _) => Self::Or(Box::new(Self::False), Box::new(Self::False)),
            Self::Implies(_, _) => Self::Implies(Box::new(Self::False), Box::new(Self::False)),
            Self::Iff(_, _) => Self::Iff(Box::new(Self::False), Box::new(Self::False)),
            Self::Forall(vars, _) => Self::Forall(vars.clone(), Box::new(Self::False)),
            Self::Exists(vars, _) => Self::Exists(vars.clone(), Box::new(Self::False)),
        }
    }

    // Bound native cleanup to eight edges before deferring deeper branches to
    // the worklist. Clearing short batches in place avoids moving this large
    // enum for every node; the bound is independent of the tree's depth.
    fn detach_children(&mut self, pending: &mut Vec<Self>, remaining: u8) {
        for child in self.children_mut() {
            if child.has_children() {
                if remaining == 0 {
                    pending.push(std::mem::replace(child, Self::False));
                } else {
                    child.detach_children(pending, remaining - 1);
                    *child = Self::False;
                }
            }
        }
    }
}

impl Clone for Formula {
    fn clone(&self) -> Self {
        let mut result = Self::False;
        let mut pending = Vec::new();
        let mut next = Some((self, &mut result));
        while let Some((source, target)) = next.take().or_else(|| pending.pop()) {
            *target = source.copy_shallow();
            if source.children().all(|child| !child.has_children()) {
                for (source, target) in source.children().zip(target.children_mut()) {
                    *target = source.copy_shallow();
                }
                continue;
            }
            for pair in source.children().rev().zip(target.children_mut().rev()) {
                if let Some(previous) = next.replace(pair) {
                    pending.push(previous);
                }
            }
        }
        result
    }
}

impl Formula {
    const DROP_BATCH_DEPTH: u8 = 8;

    fn drop_children(&mut self) {
        let mut pending = Vec::new();
        self.detach_children(&mut pending, Self::DROP_BATCH_DEPTH);
        while let Some(mut formula) = pending.pop() {
            formula.detach_children(&mut pending, Self::DROP_BATCH_DEPTH);
        }
    }
}

impl Drop for Formula {
    #[inline]
    fn drop(&mut self) {
        if self.has_children() && self.children().any(Self::has_children) {
            self.drop_children();
        }
    }
}

impl Clone for ParsedProofTree {
    fn clone(&self) -> Self {
        let mut result = Self {
            method: ParsedMethod::Sorry,
            cases: Vec::new(),
        };
        let mut pending = Vec::new();
        let mut next = Some((self, &mut result));
        while let Some((source, target)) = next.take().or_else(|| pending.pop()) {
            target.method = source.method.clone();
            target.cases = source
                .cases
                .iter()
                .map(|(name, _)| {
                    (
                        name.clone(),
                        Self {
                            method: ParsedMethod::Sorry,
                            cases: Vec::new(),
                        },
                    )
                })
                .collect();
            for ((_, source), (_, target)) in source.cases.iter().zip(target.cases.iter_mut()).rev()
            {
                if let Some(previous) = next.replace((source, target)) {
                    pending.push(previous);
                }
            }
        }
        result
    }
}

impl ParsedProofTree {
    fn drop_cases(&mut self) {
        let mut pending = std::mem::take(&mut self.cases);
        while let Some((_, mut tree)) = pending.pop() {
            pending.append(&mut tree.cases);
        }
    }
}

impl Drop for ParsedProofTree {
    #[inline]
    fn drop(&mut self) {
        if !self.cases.is_empty() {
            self.drop_cases();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Atom, Term, VarSpec};
    use tamarin_term::lterm::LSort;

    fn binder() -> VarSpec {
        VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        }
    }

    #[test]
    fn formula_clone_preserves_shapes_and_binder_depths() {
        let mut formula = Formula::Atom(Atom::Eq(Term::Number(1), Term::Number(2)));
        for i in 0..7 {
            formula = match i {
                0 => Formula::Not(Box::new(formula)),
                1 => Formula::And(Box::new(formula), Box::new(Formula::False)),
                2 => Formula::Or(Box::new(formula), Box::new(Formula::True)),
                3 => Formula::Implies(Box::new(Formula::False), Box::new(formula)),
                4 => Formula::Iff(Box::new(formula), Box::new(Formula::True)),
                5 => Formula::Forall(vec![binder(), binder()], Box::new(formula)),
                _ => Formula::Exists(vec![], Box::new(formula)),
            };
        }
        assert_eq!(formula.clone(), formula);
        let mut order = Vec::new();
        formula.visit(|f| {
            if let Formula::False = f {
                order.push(false);
            }
            if let Formula::True = f {
                order.push(true);
            }
        });
        assert_eq!(order, [false, false, true, true]);
    }

    #[test]
    fn proof_clone_preserves_case_order_and_goals() {
        let parent = crate::parser::Parser::new("", &[], false);
        let proof = crate::proof_tree::parse_proof_tree(
            "induction case left solve( P(x) @ i ) by sorry next case right SOLVED qed",
            &parent,
        )
        .unwrap();
        assert_eq!(proof.clone(), proof);
    }

    #[test]
    fn branching_formula_and_proof_lifecycles() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                // A full binary tree crosses the cleanup batch boundary with both
                // children still branching, unlike a spine with leaf siblings.
                let mut formula = Formula::True;
                let mut proof = ParsedProofTree {
                    method: ParsedMethod::SolvedLeaf,
                    cases: Vec::new(),
                };
                for _ in 0..14 {
                    formula = Formula::And(Box::new(formula.clone()), Box::new(formula));
                    proof = ParsedProofTree {
                        method: ParsedMethod::Simplify,
                        cases: vec![("left".into(), proof.clone()), ("right".into(), proof)],
                    };
                }
                let mut copy = formula.clone();
                let mut leaves = 0;
                copy.visit_mut(|node| {
                    if matches!(node, Formula::True) {
                        leaves += 1;
                        *node = Formula::False;
                    }
                    true
                });
                assert_eq!(leaves, 1 << 14);
                assert_eq!(proof.clone(), proof);
                drop((formula, copy, proof));

                let wide = ParsedProofTree {
                    method: ParsedMethod::Induction,
                    cases: (0..65_536)
                        .map(|i| {
                            (
                                i.to_string(),
                                ParsedProofTree {
                                    method: ParsedMethod::SolvedLeaf,
                                    cases: Vec::new(),
                                },
                            )
                        })
                        .collect(),
                };
                let copied = wide.clone();
                assert_eq!(copied, wide);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn deep_formula_and_proof_lifecycles_use_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = Term::NumberOne;
                for _ in 0..10_000 {
                    term = Term::PatMatch(Box::new(term));
                }
                let mut formula = Formula::Atom(Atom::Eq(term, Term::NumberOne));
                let mut proof = ParsedProofTree {
                    method: ParsedMethod::SolvedLeaf,
                    cases: Vec::new(),
                };
                for i in 0..100_000 {
                    formula = if i % 2 == 0 {
                        Formula::And(Box::new(Formula::False), Box::new(formula))
                    } else {
                        Formula::Forall(vec![binder()], Box::new(formula))
                    };
                    proof = ParsedProofTree {
                        method: ParsedMethod::Simplify,
                        cases: vec![(String::new(), proof)],
                    };
                }
                let mut copied = formula.clone();
                copied.visit_mut(|f| {
                    if matches!(f, Formula::False) {
                        *f = Formula::True;
                    }
                    true
                });
                let proof = ParsedProofTree {
                    method: ParsedMethod::Induction,
                    cases: vec![("left".into(), proof.clone()), ("right".into(), proof)],
                };
                drop(proof.clone());
                drop(proof);
                drop(copied);
                drop(formula);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
