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
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
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
                    selector =
                        SelectorExpr::And(Box::new(selector), Box::new(SelectorExpr::empty()));
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
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
