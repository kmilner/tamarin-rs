//! Iterative operations on surface terms, including cleanup after parse errors.

use crate::ast::Term;

impl Term {
    #[inline]
    pub(crate) fn children(&self) -> impl DoubleEndedIterator<Item = &Self> {
        let (many, few): (&[Self], _) = match self {
            Self::App(_, args) | Self::Pair(args) => (args, [None, None]),
            Self::AlgApp(_, a, b) | Self::Diff(a, b) | Self::BinOp(_, a, b) => {
                (&[], [Some(a.as_ref()), Some(b.as_ref())])
            }
            Self::PatMatch(t) => (&[], [Some(t.as_ref()), None]),
            _ => (&[], [None, None]),
        };
        many.iter().chain(few.into_iter().flatten())
    }

    #[inline]
    pub(crate) fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Self> {
        let (many, few): (&mut [Self], _) = match self {
            Self::App(_, args) | Self::Pair(args) => (args, [None, None]),
            Self::AlgApp(_, a, b) | Self::Diff(a, b) | Self::BinOp(_, a, b) => {
                (&mut [], [Some(a.as_mut()), Some(b.as_mut())])
            }
            Self::PatMatch(t) => (&mut [], [Some(t.as_mut()), None]),
            _ => (&mut [], [None, None]),
        };
        many.iter_mut().chain(few.into_iter().flatten())
    }

    pub(crate) fn visit(&self, mut f: impl FnMut(&Self)) {
        let mut pending = Vec::new();
        let mut next = Some(self);
        while let Some(term) = next.take().or_else(|| pending.pop()) {
            f(term);
            if term.children().all(|child| !child.has_children()) {
                for child in term.children() {
                    f(child);
                }
                continue;
            }
            for child in term.children().rev() {
                if let Some(previous) = next.replace(child) {
                    pending.push(previous);
                }
            }
        }
    }

    /// Visit in preorder; return false to skip the current node's children.
    /// Substitution uses this to avoid visiting newly inserted terms.
    pub(crate) fn visit_mut(&mut self, mut f: impl FnMut(&mut Self) -> bool) {
        let mut pending = Vec::new();
        let mut next = Some(self);
        while let Some(term) = next.take().or_else(|| pending.pop()) {
            if !f(term) {
                continue;
            }
            for child in term.children_mut().rev() {
                if let Some(previous) = next.replace(child) {
                    pending.push(previous);
                }
            }
        }
    }

    #[inline]
    fn copy_shallow(&self) -> Self {
        match self {
            Self::Var(v) => Self::Var(v.clone()),
            Self::PubLit(s) => Self::PubLit(s.clone()),
            Self::FreshLit(s) => Self::FreshLit(s.clone()),
            Self::NatLit(s) => Self::NatLit(s.clone()),
            Self::Number(n) => Self::Number(*n),
            Self::NumberOne => Self::NumberOne,
            Self::NatOne => Self::NatOne,
            Self::DhNeutral => Self::DhNeutral,
            Self::App(name, args) => Self::App(
                name.clone(),
                (0..args.len()).map(|_| Self::NumberOne).collect(),
            ),
            Self::Pair(args) => Self::Pair((0..args.len()).map(|_| Self::NumberOne).collect()),
            Self::AlgApp(name, _, _) => Self::AlgApp(
                name.clone(),
                Box::new(Self::NumberOne),
                Box::new(Self::NumberOne),
            ),
            Self::Diff(_, _) => Self::Diff(Box::new(Self::NumberOne), Box::new(Self::NumberOne)),
            Self::BinOp(op, _, _) => {
                Self::BinOp(*op, Box::new(Self::NumberOne), Box::new(Self::NumberOne))
            }
            Self::PatMatch(_) => Self::PatMatch(Box::new(Self::NumberOne)),
        }
    }

    #[inline]
    pub(crate) fn has_children(&self) -> bool {
        match self {
            Self::App(_, args) | Self::Pair(args) => !args.is_empty(),
            Self::AlgApp(..) | Self::Diff(..) | Self::BinOp(..) | Self::PatMatch(_) => true,
            _ => false,
        }
    }

    // Detach only children which themselves own children. Leaves can use the
    // ordinary destructor, keeping its call depth bounded without allocating a
    // worklist for every leaf (or every node of a unary chain).
    #[inline]
    fn detach_children(&mut self, pending: &mut Vec<Self>) -> Option<Self> {
        let mut next = None;
        for child in self.children_mut() {
            if child.has_children() {
                let detached = std::mem::replace(child, Self::NumberOne);
                if let Some(previous) = next.replace(detached) {
                    pending.push(previous);
                }
            }
        }
        if let Self::App(_, args) | Self::Pair(args) = self {
            args.clear();
        }
        next
    }

    fn drop_children(&mut self) {
        let mut pending = Vec::new();
        let mut next = self.detach_children(&mut pending);
        while let Some(mut term) = next.take().or_else(|| pending.pop()) {
            next = term.detach_children(&mut pending);
        }
    }
}

impl Clone for Term {
    fn clone(&self) -> Self {
        let mut result = Self::NumberOne;
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
            // Keep the next child inline; unary chains need no worklist allocation.
            for pair in source.children().rev().zip(target.children_mut().rev()) {
                if let Some(previous) = next.replace(pair) {
                    pending.push(previous);
                }
            }
        }
        result
    }
}

impl Drop for Term {
    #[inline]
    fn drop(&mut self) {
        if self.has_children() {
            self.drop_children();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp, VarSpec};
    use tamarin_term::lterm::LSort;

    #[test]
    fn copy_preserves_every_term_shape_and_child_order() {
        let variable = Term::Var(VarSpec {
            name: "x".into(),
            idx: 3,
            sort: LSort::Msg,
            typ: Some("bytes".into()),
        });
        let term = Term::App(
            "f".into(),
            vec![
                variable,
                Term::PubLit("public".into()),
                Term::FreshLit("fresh".into()),
                Term::NatLit("natural".into()),
                Term::Number(42),
                Term::NumberOne,
                Term::NatOne,
                Term::DhNeutral,
                Term::AlgApp(
                    "g".into(),
                    Box::new(Term::Number(1)),
                    Box::new(Term::Number(2)),
                ),
                Term::Pair(vec![Term::Number(3), Term::Number(4), Term::Number(5)]),
                Term::Diff(Box::new(Term::Number(6)), Box::new(Term::Number(7))),
                Term::BinOp(
                    BinOp::Exp,
                    Box::new(Term::Number(8)),
                    Box::new(Term::Number(9)),
                ),
                Term::PatMatch(Box::new(Term::Number(10))),
                Term::Pair(vec![]),
                Term::App("empty".into(), vec![]),
            ],
        );
        assert_eq!(term.clone(), term);
        let mut numbers = Vec::new();
        term.visit(|t| {
            if let Term::Number(n) = t {
                numbers.push(*n);
            }
        });
        assert_eq!(numbers, [42, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
        let mut mutated = term.clone();
        mutated.visit_mut(|t| {
            if let Term::Number(n) = t {
                *n = 99;
            }
            true
        });
        let mut numbers = Vec::new();
        mutated.visit(|t| {
            if let Term::Number(n) = t {
                numbers.push(*n);
            }
        });
        assert_eq!(numbers, [99; 11]);
    }

    #[test]
    fn deep_term_lifecycle_uses_bounded_native_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = Term::Number(0);
                for i in 0..100_000 {
                    term = match i % 5 {
                        0 => Term::App("f".into(), vec![term]),
                        1 => Term::Pair(vec![Term::Number(1), term]),
                        2 => Term::Diff(Box::new(term), Box::new(Term::Number(2))),
                        3 => Term::BinOp(BinOp::Exp, Box::new(Term::Number(3)), Box::new(term)),
                        _ => Term::PatMatch(Box::new(term)),
                    };
                }
                // An interrupted rewrite must also destroy the tree without
                // recursively unwinding its modified prefix.
                let mut visited = 0;
                let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut interrupted = term.clone();
                    interrupted.visit_mut(|node| {
                        visited += 1;
                        assert!(visited < 50_000, "interrupted substitution");
                        if let Term::Number(n) = node {
                            *n += 1;
                        }
                        true
                    });
                }));
                assert!(failed.is_err());
                let mut copied = term.clone();
                copied.visit_mut(|t| {
                    if let Term::Number(n) = t {
                        *n += 1;
                    }
                    true
                });
                let mut replaced = term.clone();
                replaced.visit_mut(|t| {
                    if matches!(t, Term::Number(0)) {
                        *t = Term::Number(42);
                        false
                    } else {
                        true
                    }
                });
                drop(replaced);
                drop(copied);
                drop(term);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn replacement_subtrees_are_not_revisited() {
        let term = Term::App("f".into(), vec![Term::Number(1)]);
        let mut copied = term.clone();
        copied.visit_mut(|t| {
            if matches!(t, Term::Number(1)) {
                *t = term.clone();
                false
            } else {
                true
            }
        });
        assert_eq!(copied, Term::App("f".into(), vec![term]));
    }
}
