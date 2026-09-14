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

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = Vec::new();
        let mut next = Some((self, other));
        while let Some((left, right)) = next.take().or_else(|| pending.pop()) {
            match (left, right) {
                (Self::False, Self::False) | (Self::True, Self::True) => {}
                (Self::Atom(a), Self::Atom(b)) if a == b => {}
                (Self::Not(a), Self::Not(b)) => next = Some((a, b)),
                (Self::And(a1, a2), Self::And(b1, b2))
                | (Self::Or(a1, a2), Self::Or(b1, b2))
                | (Self::Implies(a1, a2), Self::Implies(b1, b2))
                | (Self::Iff(a1, a2), Self::Iff(b1, b2)) => {
                    pending.push((a2, b2));
                    next = Some((a1, b1));
                }
                (Self::Forall(av, a), Self::Forall(bv, b))
                | (Self::Exists(av, a), Self::Exists(bv, b))
                    if av == bv =>
                {
                    next = Some((a, b));
                }
                _ => return false,
            }
        }
        true
    }
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Self::False => f.write_str("False"),
                Self::True => f.write_str("True"),
                Self::Atom(atom) => f.debug_tuple("Atom").field(atom).finish(),
                Self::Not(body) => f.debug_tuple("Not").field(body).finish(),
                Self::And(left, right) => f.debug_tuple("And").field(left).field(right).finish(),
                Self::Or(left, right) => f.debug_tuple("Or").field(left).field(right).finish(),
                Self::Implies(left, right) => {
                    f.debug_tuple("Implies").field(left).field(right).finish()
                }
                Self::Iff(left, right) => f.debug_tuple("Iff").field(left).field(right).finish(),
                Self::Forall(vars, body) => {
                    f.debug_tuple("Forall").field(vars).field(body).finish()
                }
                Self::Exists(vars, body) => {
                    f.debug_tuple("Exists").field(vars).field(body).finish()
                }
            })
        })
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

impl PartialEq for ParsedProofTree {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.method != right.method || left.cases.len() != right.cases.len() {
                return false;
            }
            for ((left_name, left_child), (right_name, right_child)) in
                left.cases.iter().zip(&right.cases).rev()
            {
                if left_name != right_name {
                    return false;
                }
                pending.push((left_child, right_child));
            }
        }
        true
    }
}

impl std::fmt::Debug for ParsedProofTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            tamarin_utils::stack::ensure_sufficient_stack(|| {
                f.debug_struct("ParsedProofTree")
                    .field("method", &self.method)
                    .field("cases", &self.cases)
                    .finish()
            })
        })
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
#[path = "formula_walk_tests.rs"]
mod tests;
