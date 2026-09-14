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

// Compare shallow fields first, then reuse the surface child ordering. Protect
// equality itself: duplicate rules and other derived AST comparisons call it.
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = Vec::new();
        let mut next = Some((self, other));
        while let Some((left, right)) = next.take().or_else(|| pending.pop()) {
            let same_head = match (left, right) {
                (Self::Var(a), Self::Var(b)) => a == b,
                (Self::PubLit(a), Self::PubLit(b))
                | (Self::FreshLit(a), Self::FreshLit(b))
                | (Self::NatLit(a), Self::NatLit(b)) => a == b,
                (Self::Number(a), Self::Number(b)) => a == b,
                (Self::NumberOne, Self::NumberOne)
                | (Self::NatOne, Self::NatOne)
                | (Self::DhNeutral, Self::DhNeutral)
                | (Self::Diff(..), Self::Diff(..))
                | (Self::PatMatch(_), Self::PatMatch(_)) => true,
                (Self::App(a, xs), Self::App(b, ys)) => a == b && xs.len() == ys.len(),
                (Self::Pair(xs), Self::Pair(ys)) => xs.len() == ys.len(),
                (Self::AlgApp(a, ..), Self::AlgApp(b, ..)) => a == b,
                (Self::BinOp(a, ..), Self::BinOp(b, ..)) => a == b,
                _ => false,
            };
            if !same_head {
                return false;
            }
            // Keep a unary continuation inline, avoiding a heap worklist for it.
            for pair in left.children().rev().zip(right.children().rev()) {
                if let Some(previous) = next.replace(pair) {
                    pending.push(previous);
                }
            }
        }
        true
    }
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Self::Var(value) => f.debug_tuple("Var").field(value).finish(),
                Self::PubLit(value) => f.debug_tuple("PubLit").field(value).finish(),
                Self::FreshLit(value) => f.debug_tuple("FreshLit").field(value).finish(),
                Self::NatLit(value) => f.debug_tuple("NatLit").field(value).finish(),
                Self::Number(value) => f.debug_tuple("Number").field(value).finish(),
                Self::NumberOne => f.write_str("NumberOne"),
                Self::NatOne => f.write_str("NatOne"),
                Self::DhNeutral => f.write_str("DhNeutral"),
                Self::App(name, args) => f.debug_tuple("App").field(name).field(args).finish(),
                Self::AlgApp(name, left, right) => f
                    .debug_tuple("AlgApp")
                    .field(name)
                    .field(left)
                    .field(right)
                    .finish(),
                Self::Pair(args) => f.debug_tuple("Pair").field(args).finish(),
                Self::Diff(left, right) => f.debug_tuple("Diff").field(left).field(right).finish(),
                Self::BinOp(op, left, right) => f
                    .debug_tuple("BinOp")
                    .field(op)
                    .field(left)
                    .field(right)
                    .finish(),
                Self::PatMatch(term) => f.debug_tuple("PatMatch").field(term).finish(),
            })
        })
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
#[path = "term_walk_tests.rs"]
mod tests;
