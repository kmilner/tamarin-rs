//! Bounded-stack lifecycle operations for rule and selector trees.

use crate::ast::{Rule, SelectorExpr, SelectorLeaf};

impl Rule {
    fn children(&self) -> impl DoubleEndedIterator<Item = &Self> {
        self.variants.iter().chain(
            self.left_right
                .iter()
                .flat_map(|(a, b)| [a.as_ref(), b.as_ref()]),
        )
    }

    fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Self> {
        self.variants.iter_mut().chain(
            self.left_right
                .iter_mut()
                .flat_map(|(a, b)| [a.as_mut(), b.as_mut()]),
        )
    }

    fn copy_shallow(&self) -> Self {
        Self {
            name: self.name.clone(),
            modulo: self.modulo.clone(),
            attributes: self.attributes.clone(),
            premises: self.premises.clone(),
            actions: self.actions.clone(),
            conclusions: self.conclusions.clone(),
            embedded_restrictions: self.embedded_restrictions.clone(),
            variants: self.variants.iter().map(|_| Self::default()).collect(),
            left_right: self
                .left_right
                .as_ref()
                .map(|_| (Box::default(), Box::default())),
        }
    }

    fn detach_children(&mut self, pending: &mut Vec<Self>) {
        pending.append(&mut self.variants);
        if let Some((left, right)) = self.left_right.take() {
            pending.push(*left);
            pending.push(*right);
        }
    }
}

impl Clone for Rule {
    fn clone(&self) -> Self {
        let mut result = Self::default();
        let mut pending = Vec::new();
        let mut next = Some((self, &mut result));
        while let Some((source, target)) = next.take().or_else(|| pending.pop()) {
            *target = source.copy_shallow();
            for pair in source.children().rev().zip(target.children_mut().rev()) {
                if let Some(previous) = next.replace(pair) {
                    pending.push(previous);
                }
            }
        }
        result
    }
}

impl std::fmt::Debug for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            tamarin_utils::stack::ensure_sufficient_stack(|| {
                f.debug_struct("Rule")
                    .field("name", &self.name)
                    .field("modulo", &self.modulo)
                    .field("attributes", &self.attributes)
                    .field("premises", &self.premises)
                    .field("actions", &self.actions)
                    .field("conclusions", &self.conclusions)
                    .field("embedded_restrictions", &self.embedded_restrictions)
                    .field("variants", &self.variants)
                    .field("left_right", &self.left_right)
                    .finish()
            })
        })
    }
}

impl Drop for Rule {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.variants);
        self.detach_children(&mut pending);
        while let Some(mut rule) = pending.pop() {
            rule.detach_children(&mut pending);
        }
    }
}

impl SelectorExpr {
    fn empty() -> Self {
        Self::Leaf(SelectorLeaf {
            name: String::new(),
            params: Vec::new(),
        })
    }

    pub(crate) fn children(&self) -> impl DoubleEndedIterator<Item = &Self> {
        match self {
            Self::Leaf(_) => [None, None],
            Self::Not(a) => [Some(a.as_ref()), None],
            Self::And(a, b) | Self::Or(a, b) => [Some(a.as_ref()), Some(b.as_ref())],
        }
        .into_iter()
        .flatten()
    }

    fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Self> {
        match self {
            Self::Leaf(_) => [None, None],
            Self::Not(a) => [Some(a.as_mut()), None],
            Self::And(a, b) | Self::Or(a, b) => [Some(a.as_mut()), Some(b.as_mut())],
        }
        .into_iter()
        .flatten()
    }

    fn copy_shallow(&self) -> Self {
        match self {
            Self::Leaf(leaf) => Self::Leaf(leaf.clone()),
            Self::Not(_) => Self::Not(Box::new(Self::empty())),
            Self::And(_, _) => Self::And(Box::new(Self::empty()), Box::new(Self::empty())),
            Self::Or(_, _) => Self::Or(Box::new(Self::empty()), Box::new(Self::empty())),
        }
    }

    fn detach_children(&mut self, pending: &mut Vec<Self>) {
        for child in self.children_mut() {
            if !matches!(child, Self::Leaf(_)) {
                pending.push(std::mem::replace(child, Self::empty()));
            }
        }
    }
}

impl Clone for SelectorExpr {
    fn clone(&self) -> Self {
        let mut result = Self::empty();
        let mut pending = Vec::new();
        let mut next = Some((self, &mut result));
        while let Some((source, target)) = next.take().or_else(|| pending.pop()) {
            *target = source.copy_shallow();
            for pair in source.children().rev().zip(target.children_mut().rev()) {
                if let Some(previous) = next.replace(pair) {
                    pending.push(previous);
                }
            }
        }
        result
    }
}

impl PartialEq for SelectorExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = Vec::new();
        let mut next = Some((self, other));
        while let Some((left, right)) = next.take().or_else(|| pending.pop()) {
            match (left, right) {
                (Self::Leaf(a), Self::Leaf(b)) if a == b => {}
                (Self::Not(a), Self::Not(b)) => next = Some((a, b)),
                (Self::And(a1, a2), Self::And(b1, b2)) | (Self::Or(a1, a2), Self::Or(b1, b2)) => {
                    pending.push((a2, b2));
                    next = Some((a1, b1));
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for SelectorExpr {}

impl std::fmt::Debug for SelectorExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Self::Leaf(leaf) => f.debug_tuple("Leaf").field(leaf).finish(),
                Self::Not(expr) => f.debug_tuple("Not").field(expr).finish(),
                Self::And(left, right) => f.debug_tuple("And").field(left).field(right).finish(),
                Self::Or(left, right) => f.debug_tuple("Or").field(left).field(right).finish(),
            })
        })
    }
}

impl Drop for SelectorExpr {
    fn drop(&mut self) {
        if matches!(self, Self::Leaf(_)) {
            return;
        }
        let mut pending = Vec::new();
        self.detach_children(&mut pending);
        while let Some(mut expr) = pending.pop() {
            expr.detach_children(&mut pending);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rule_and_selector_lifecycles_use_bounded_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            let mut rule = Rule::default();
            rule.name = "leaf".into();
            let mut selector = SelectorExpr::Leaf(SelectorLeaf {
                name: "regex".into(),
                params: vec!["x".into()],
            });
            for i in 0..100_000 {
                let mut parent = Rule::default();
                if i % 2 == 0 {
                    parent.variants.push(rule);
                } else {
                    parent.left_right = Some((Box::default(), Box::new(rule)));
                }
                rule = parent;
                selector = SelectorExpr::And(Box::new(selector), Box::new(SelectorExpr::empty()));
            }
            drop(rule.clone());
            drop(rule);
            let copy = selector.clone();
            drop((selector, copy));

            let mut rule = Rule::default();
            rule.name = "named".into();
            let mut selector = SelectorExpr::Not(Box::new(SelectorExpr::empty()));
            for _ in 0..8 {
                let mut parent = Rule::default();
                parent.variants = vec![rule.clone()];
                parent.left_right = Some((Box::new(rule.clone()), Box::new(rule)));
                rule = parent;
                selector = SelectorExpr::Or(Box::new(selector.clone()), Box::new(selector));
            }
            assert_eq!(rule.clone(), rule);
            assert_eq!(selector.clone(), selector);
        });
    }

    #[test]
    fn deep_selector_comparison_and_recursive_debug_use_bounded_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            let leaf = || {
                SelectorExpr::Leaf(SelectorLeaf {
                    name: "x".into(),
                    params: Vec::new(),
                })
            };
            let mut selector = leaf();
            let mut rule = Rule::default();
            for _ in 0..8192 {
                selector = SelectorExpr::And(Box::new(selector), Box::new(leaf()));
                let mut parent = Rule::default();
                parent.variants.push(rule);
                rule = parent;
            }
            assert_eq!(selector, selector.clone());
            assert!(format!("{selector:?}").starts_with("And("));
            assert_eq!(format!("{selector:#?}").matches("And(").count(), 8192);
            assert!(format!("{rule:?}").starts_with("Rule {"));
            assert_eq!(format!("{rule:#?}").matches("Rule {").count(), 8193);
        });
    }
}
