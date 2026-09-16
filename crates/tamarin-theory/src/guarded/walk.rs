//! Borrowed walks and copy-on-write rebuilding of guarded formula spines.
use super::Guarded;
use std::ops::ControlFlow;

pub(super) fn children(g: &Guarded) -> &[Guarded] {
    match g {
        Guarded::Atom(_) => &[],
        Guarded::Disj(xs) | Guarded::Conj(xs) => xs,
        Guarded::GGuarded { body, .. } => std::slice::from_ref(body),
    }
}
pub(super) fn visit<B>(
    g: &Guarded,
    mut f: impl FnMut(usize, &Guarded) -> ControlFlow<B, bool>,
) -> ControlFlow<B> {
    let mut current = (std::slice::from_ref(g), 1usize);
    let mut pending = Vec::new();
    loop {
        while let Some((g, rest)) = current.0.split_first() {
            current.0 = rest;
            if f(current.1, g)? && !children(g).is_empty() {
                if !rest.is_empty() {
                    pending.push(current);
                }
                current = (children(g), current.1.saturating_add(1));
            }
        }
        let Some(next) = pending.pop() else {
            return ControlFlow::Continue(());
        };
        current = next;
    }
}
pub(super) enum Step<'a, P> {
    Done(Option<Guarded>),
    Descend(u64, P),
    DescendChildren(u64, P, Vec<&'a Guarded>),
}

/// Children are rebuilt left to right. The output vector is allocated only
/// when a child changes; unchanged prefixes are cloned once on that first change.
pub(super) fn rewrite<'a, P, E>(
    g: &'a Guarded,
    pre: &mut impl FnMut(u64, &'a Guarded) -> Result<Step<'a, P>, E>,
    post: &mut impl FnMut(&Guarded, P, Option<Vec<Guarded>>) -> Result<Option<Guarded>, E>,
) -> Result<Option<Guarded>, E> {
    enum Children<'a> {
        Direct(&'a [Guarded]),
        Selected(Vec<&'a Guarded>),
    }
    impl<'a> Children<'a> {
        fn get(&self, index: usize) -> Option<&'a Guarded> {
            match self {
                Self::Direct(xs) => xs.get(index),
                Self::Selected(xs) => xs.get(index).copied(),
            }
        }
        fn len(&self) -> usize {
            match self {
                Self::Direct(xs) => xs.len(),
                Self::Selected(xs) => xs.len(),
            }
        }
    }
    struct Frame<'a, P> {
        children: Children<'a>,
        node: &'a Guarded,
        scope: u64,
        context: P,
        index: usize,
        mapped: Option<Vec<Guarded>>,
    }
    // A flat rewrite keeps its active frame here; allocate only to suspend
    // a parent while descending into another non-leaf node.
    let mut frame = None;
    let mut parents = Vec::new();
    let mut current = (g, 0);
    loop {
        let (node, scope) = current;
        let mut result = match pre(scope, node)? {
            Step::Done(result) => result,
            step => {
                let (scope, context, selected) = match step {
                    Step::Descend(scope, context) => {
                        (scope, context, Children::Direct(children(node)))
                    }
                    Step::DescendChildren(scope, context, selected) => {
                        (scope, context, Children::Selected(selected))
                    }
                    Step::Done(_) => unreachable!(),
                };
                if let Some(first) = selected.get(0) {
                    let mapped = if matches!(&selected, Children::Selected(_)) {
                        Some(Vec::with_capacity(selected.len()))
                    } else {
                        None
                    };
                    let next = Frame {
                        children: selected,
                        node,
                        scope,
                        context,
                        index: 0,
                        mapped,
                    };
                    if let Some(parent) = frame.replace(next) {
                        parents.push(parent);
                    }
                    current = (first, scope);
                    continue;
                }
                post(
                    node,
                    context,
                    if matches!(selected, Children::Selected(_)) {
                        Some(Vec::new())
                    } else {
                        None
                    },
                )?
            }
        };
        loop {
            let Some(active) = frame.as_mut() else {
                return Ok(result);
            };
            let original = &active.children;
            if let Some(mapped) = &mut active.mapped {
                mapped.push(result.unwrap_or_else(|| original.get(active.index).unwrap().clone()));
            } else if let Some(result) = result {
                let mut mapped = Vec::with_capacity(original.len());
                mapped.extend((0..active.index).map(|i| original.get(i).unwrap().clone()));
                mapped.push(result);
                active.mapped = Some(mapped);
            }
            active.index += 1;
            if active.index < original.len() {
                current = (original.get(active.index).unwrap(), active.scope);
                break;
            }
            let completed = frame.take().unwrap();
            frame = parents.pop();
            result = post(completed.node, completed.context, completed.mapped)?;
        }
    }
}
