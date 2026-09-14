//! Bounded-stack cloning and destruction of surface processes.

use crate::ast::Process;

impl Process {
    #[inline]
    fn has_children(&self) -> bool {
        !matches!(self, Self::Null | Self::Call { .. })
    }

    #[inline]
    pub(crate) fn children(&self) -> impl DoubleEndedIterator<Item = &Self> {
        let children = match self {
            Self::Action { body, .. } | Self::Replication(body) | Self::AtAnnotation(body, _) => {
                [Some(body.as_ref()), None]
            }
            Self::Comb { left, right, .. } => [Some(left.as_ref()), Some(right.as_ref())],
            Self::Null | Self::Call { .. } => [None, None],
        };
        children.into_iter().flatten()
    }

    #[inline]
    fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Self> {
        let children = match self {
            Self::Action { body, .. } | Self::Replication(body) | Self::AtAnnotation(body, _) => {
                [Some(body.as_mut()), None]
            }
            Self::Comb { left, right, .. } => [Some(left.as_mut()), Some(right.as_mut())],
            Self::Null | Self::Call { .. } => [None, None],
        };
        children.into_iter().flatten()
    }

    #[inline]
    fn copy_shallow(&self) -> Self {
        match self {
            Self::Null => Self::Null,
            Self::Call { name, args } => Self::Call {
                name: name.clone(),
                args: args.clone(),
            },
            Self::Action { action, .. } => Self::Action {
                action: action.clone(),
                body: Box::new(Self::Null),
            },
            Self::Comb { comb, .. } => Self::Comb {
                comb: comb.clone(),
                left: Box::new(Self::Null),
                right: Box::new(Self::Null),
            },
            Self::Replication(_) => Self::Replication(Box::new(Self::Null)),
            Self::AtAnnotation(_, term) => Self::AtAnnotation(Box::new(Self::Null), term.clone()),
        }
    }

    // As for formulas, clear short batches in place, deferring deeper branches
    // to a heap worklist. The native call depth never depends on input depth.
    fn detach_children(&mut self, pending: &mut Vec<Self>, remaining: u8) {
        for child in self.children_mut() {
            if child.has_children() {
                if remaining == 0 {
                    pending.push(std::mem::replace(child, Self::Null));
                } else {
                    child.detach_children(pending, remaining - 1);
                    *child = Self::Null;
                }
            }
        }
    }

    fn drop_children(&mut self) {
        const BATCH_DEPTH: u8 = 8;
        let mut pending = Vec::new();
        self.detach_children(&mut pending, BATCH_DEPTH);
        while let Some(mut process) = pending.pop() {
            process.detach_children(&mut pending, BATCH_DEPTH);
        }
    }
}

impl Clone for Process {
    fn clone(&self) -> Self {
        let mut result = Self::Null;
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

impl PartialEq for Process {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = Vec::new();
        let mut next = Some((self, other));
        while let Some((left, right)) = next.take().or_else(|| pending.pop()) {
            match (left, right) {
                (Self::Null, Self::Null) => {}
                (
                    Self::Action {
                        action: left_action,
                        body: left_body,
                    },
                    Self::Action {
                        action: right_action,
                        body: right_body,
                    },
                ) if left_action == right_action => next = Some((left_body, right_body)),
                (
                    Self::Comb {
                        comb: left_comb,
                        left: left_first,
                        right: left_second,
                    },
                    Self::Comb {
                        comb: right_comb,
                        left: right_first,
                        right: right_second,
                    },
                ) if left_comb == right_comb => {
                    pending.push((left_second, right_second));
                    next = Some((left_first, right_first));
                }
                (Self::Replication(left), Self::Replication(right)) => {
                    next = Some((left, right));
                }
                (
                    Self::Call {
                        name: left_name,
                        args: left_args,
                    },
                    Self::Call {
                        name: right_name,
                        args: right_args,
                    },
                ) if left_name == right_name && left_args == right_args => {}
                (Self::AtAnnotation(left, left_term), Self::AtAnnotation(right, right_term))
                    if left_term == right_term =>
                {
                    next = Some((left, right));
                }
                _ => return false,
            }
        }
        true
    }
}

impl std::fmt::Debug for Process {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Self::Null => f.write_str("Null"),
                Self::Action { action, body } => f
                    .debug_struct("Action")
                    .field("action", action)
                    .field("body", body)
                    .finish(),
                Self::Comb { comb, left, right } => f
                    .debug_struct("Comb")
                    .field("comb", comb)
                    .field("left", left)
                    .field("right", right)
                    .finish(),
                Self::Replication(body) => f.debug_tuple("Replication").field(body).finish(),
                Self::Call { name, args } => f
                    .debug_struct("Call")
                    .field("name", name)
                    .field("args", args)
                    .finish(),
                Self::AtAnnotation(body, term) => f
                    .debug_tuple("AtAnnotation")
                    .field(body)
                    .field(term)
                    .finish(),
            })
        })
    }
}

impl Drop for Process {
    #[inline]
    fn drop(&mut self) {
        if self.has_children() && self.children().any(Self::has_children) {
            self.drop_children();
        }
    }
}

#[cfg(test)]
#[path = "process_walk_tests.rs"]
mod tests;
