//! Shared guarded-formula edges with iterative last-owner destruction.
use super::Guarded;
use std::sync::Arc;

#[derive(Clone)]
pub struct GuardedChildren(Arc<OwnedChildren>);
struct OwnedChildren(Vec<Guarded>);
#[derive(Clone)]
pub struct GuardedBody(Arc<OwnedBody>);
struct OwnedBody(Option<Guarded>);

impl From<Vec<Guarded>> for GuardedChildren {
    fn from(items: Vec<Guarded>) -> Self {
        Self(Arc::new(OwnedChildren(items)))
    }
}
impl FromIterator<Guarded> for GuardedChildren {
    fn from_iter<I: IntoIterator<Item = Guarded>>(items: I) -> Self {
        Vec::from_iter(items).into()
    }
}
impl std::ops::Deref for GuardedChildren {
    type Target = [Guarded];
    fn deref(&self) -> &[Guarded] {
        &self.0 .0
    }
}
impl AsRef<[Guarded]> for GuardedChildren {
    fn as_ref(&self) -> &[Guarded] {
        self
    }
}
impl GuardedBody {
    pub fn new(value: Guarded) -> Self {
        Self(Arc::new(OwnedBody(Some(value))))
    }
}
impl std::ops::Deref for GuardedBody {
    type Target = Guarded;
    fn deref(&self) -> &Guarded {
        self.0 .0.as_ref().unwrap()
    }
}
impl AsRef<Guarded> for GuardedBody {
    fn as_ref(&self) -> &Guarded {
        self
    }
}

// Arc::into_inner, rather than try_unwrap + dropping Err, also handles
// concurrent last-owner release without re-entering a deep destructor.
fn release(mut current: Option<Guarded>, items: Vec<Guarded>) {
    let mut siblings = items.into_iter();
    let mut pending = Vec::new();
    loop {
        let Some(node) = current.take().or_else(|| siblings.next()) else {
            let Some(next) = pending.pop() else { return };
            siblings = next;
            continue;
        };
        match node {
            Guarded::Atom(_) => {}
            Guarded::Conj(items) | Guarded::Disj(items) => {
                if let Some(items) = Arc::into_inner(items.0) {
                    let mut items = std::mem::ManuallyDrop::new(items);
                    let children = std::mem::take(&mut items.0).into_iter();
                    if siblings.as_slice().is_empty() {
                        siblings = children;
                    } else if !children.as_slice().is_empty() {
                        pending.push(std::mem::replace(&mut siblings, children));
                    }
                }
            }
            Guarded::GGuarded { body, .. } => {
                if let Some(body) = Arc::into_inner(body.0) {
                    let mut body = std::mem::ManuallyDrop::new(body);
                    current = body.0.take();
                }
            }
        }
    }
}
impl Drop for OwnedChildren {
    fn drop(&mut self) {
        release(None, std::mem::take(&mut self.0));
    }
}
impl Drop for OwnedBody {
    fn drop(&mut self) {
        release(self.0.take(), Vec::new());
    }
}

macro_rules! edge_traits {
    ($edge:ty) => {
        impl PartialEq for $edge {
            fn eq(&self, other: &Self) -> bool {
                Arc::ptr_eq(&self.0, &other.0) || **self == **other
            }
        }
        impl Eq for $edge {}
        impl PartialOrd for $edge {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $edge {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                if Arc::ptr_eq(&self.0, &other.0) {
                    std::cmp::Ordering::Equal
                } else {
                    (**self).cmp(&**other)
                }
            }
        }
        impl std::hash::Hash for $edge {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                std::hash::Hash::hash(&**self, state)
            }
        }
        impl std::fmt::Debug for $edge {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Debug::fmt(&**self, f)
            }
        }
    };
}
edge_traits!(GuardedChildren);
edge_traits!(GuardedBody);

impl PartialEq for Guarded {
    fn eq(&self, other: &Self) -> bool {
        compare(self, other, true) == std::cmp::Ordering::Equal
    }
}
impl Eq for Guarded {}
impl PartialOrd for Guarded {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Guarded {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        compare(self, other, false)
    }
}
fn compare(left: &Guarded, right: &Guarded, equality: bool) -> std::cmp::Ordering {
    use std::cmp::Ordering::{Equal, Less};
    fn tag(g: &Guarded) -> u8 {
        match g {
            Guarded::Atom(_) => 0,
            Guarded::Disj(_) => 1,
            Guarded::Conj(_) => 2,
            Guarded::GGuarded { .. } => 3,
        }
    }
    enum Work<'a> {
        Pair(&'a Guarded, &'a Guarded),
        Children(&'a [Guarded], &'a [Guarded]),
    }
    let mut pending = Vec::new();
    let mut current = Some(Work::Pair(left, right));
    while let Some(work) = current.take().or_else(|| pending.pop()) {
        let order = match work {
            Work::Children(a, b) => match (a.split_first(), b.split_first()) {
                (Some((a, rest_a)), Some((b, rest_b))) => {
                    if !rest_a.is_empty() || !rest_b.is_empty() {
                        pending.push(Work::Children(rest_a, rest_b));
                    }
                    current = Some(Work::Pair(a, b));
                    Equal
                }
                _ => a.len().cmp(&b.len()),
            },
            Work::Pair(a, b) => {
                let order = tag(a).cmp(&tag(b));
                if order != Equal {
                    return order;
                }
                match (a, b) {
                    (Guarded::Atom(a), Guarded::Atom(b)) => {
                        if equality {
                            if a == b {
                                Equal
                            } else {
                                Less
                            }
                        } else {
                            a.cmp(b)
                        }
                    }
                    (Guarded::Disj(a), Guarded::Disj(b)) | (Guarded::Conj(a), Guarded::Conj(b)) => {
                        // Equality rejects unequal lengths before inspecting any
                        // child. Ordering compares only the prefix it needs.
                        if equality && a.len() != b.len() {
                            return Less;
                        }
                        if !Arc::ptr_eq(&a.0, &b.0) {
                            current = Some(Work::Children(a, b));
                        }
                        Equal
                    }
                    (
                        Guarded::GGuarded {
                            qua: q,
                            vars: v,
                            guards: g,
                            body: b,
                        },
                        Guarded::GGuarded {
                            qua: r,
                            vars: w,
                            guards: h,
                            body: c,
                        },
                    ) => {
                        let order = if equality {
                            if q == r && v == w && g == h {
                                Equal
                            } else {
                                Less
                            }
                        } else {
                            q.cmp(r).then_with(|| v.cmp(w)).then_with(|| g.cmp(h))
                        };
                        if order != Equal {
                            return order;
                        }
                        if !Arc::ptr_eq(&b.0, &c.0) {
                            current = Some(Work::Pair(b, c));
                        }
                        Equal
                    }
                    _ => unreachable!(),
                }
            }
        };
        if order != Equal {
            return order;
        }
    }
    Equal
}
impl std::hash::Hash for Guarded {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut pending = Vec::new();
        let mut current = Some(self);
        while let Some(node) = current.take().or_else(|| pending.pop()) {
            std::mem::discriminant(node).hash(state);
            match node {
                Guarded::Atom(a) => a.hash(state),
                Guarded::Disj(items) | Guarded::Conj(items) => {
                    items.len().hash(state);
                    if let Some((first, rest)) = items.split_first() {
                        pending.extend(rest.iter().rev());
                        current = Some(first);
                    }
                }
                Guarded::GGuarded {
                    qua,
                    vars,
                    guards,
                    body,
                } => {
                    qua.hash(state);
                    vars.hash(state);
                    guards.hash(state);
                    current = Some(body);
                }
            }
        }
    }
}
impl std::fmt::Debug for Guarded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            return tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Guarded::Atom(a) => f.debug_tuple("Atom").field(a).finish(),
                Guarded::Disj(a) => f.debug_tuple("Disj").field(a).finish(),
                Guarded::Conj(a) => f.debug_tuple("Conj").field(a).finish(),
                Guarded::GGuarded {
                    qua,
                    vars,
                    guards,
                    body,
                } => f
                    .debug_struct("GGuarded")
                    .field("qua", qua)
                    .field("vars", vars)
                    .field("guards", guards)
                    .field("body", body)
                    .finish(),
            });
        }
        enum Work<'a> {
            Node(&'a Guarded),
            Text(&'static str),
        }
        let mut pending = vec![Work::Node(self)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Text(s) => f.write_str(s)?,
                Work::Node(node) => match node {
                    Guarded::Atom(a) => {
                        f.debug_tuple("Atom").field(a).finish()?;
                    }
                    Guarded::Disj(items) | Guarded::Conj(items) => {
                        f.write_str(if matches!(node, Guarded::Disj(_)) {
                            "Disj(["
                        } else {
                            "Conj(["
                        })?;
                        pending.push(Work::Text("])"));
                        for (i, item) in items.iter().enumerate().rev() {
                            pending.push(Work::Node(item));
                            if i > 0 {
                                pending.push(Work::Text(", "));
                            }
                        }
                    }
                    Guarded::GGuarded {
                        qua,
                        vars,
                        guards,
                        body,
                    } => {
                        f.write_str("GGuarded { qua: ")?;
                        std::fmt::Debug::fmt(qua, f)?;
                        f.write_str(", vars: ")?;
                        std::fmt::Debug::fmt(vars, f)?;
                        f.write_str(", guards: ")?;
                        std::fmt::Debug::fmt(guards, f)?;
                        f.write_str(", body: ")?;
                        pending.push(Work::Text(" }"));
                        pending.push(Work::Node(body));
                    }
                },
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{Atom, ProtoAtom};
    use crate::formula::{BLNTerm, Quantifier};
    use crate::guarded::*;
    use std::hash::{Hash, Hasher};
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum Reference {
        Atom(Atom<BLNTerm>),
        Disj(Vec<Reference>),
        Conj(Vec<Reference>),
        GGuarded {
            qua: Quantifier,
            vars: Vec<(String, LSort)>,
            guards: Vec<Atom<BLNTerm>>,
            body: Box<Reference>,
        },
    }
    fn reference(g: &Guarded) -> Reference {
        match g {
            Guarded::Atom(a) => Reference::Atom(a.clone()),
            Guarded::Disj(xs) => Reference::Disj(xs.iter().map(reference).collect()),
            Guarded::Conj(xs) => Reference::Conj(xs.iter().map(reference).collect()),
            Guarded::GGuarded {
                qua,
                vars,
                guards,
                body,
            } => Reference::GGuarded {
                qua: *qua,
                vars: vars.to_vec(),
                guards: guards.to_vec(),
                body: Box::new(reference(body)),
            },
        }
    }
    fn atom() -> Guarded {
        let t = var_term(BVar::Free(LVar::new("x", LSort::Msg, 0)));
        Guarded::Atom(ProtoAtom::EqE(t.clone(), t))
    }
    fn binder(body: Guarded) -> Guarded {
        Guarded::GGuarded {
            qua: Quantifier::All,
            vars: vec![("v".into(), LSort::Msg)].into(),
            guards: vec![].into(),
            body: GuardedBody::new(body),
        }
    }
    #[derive(Default)]
    struct Writes(Vec<Vec<u8>>);
    impl Hasher for Writes {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.push(bytes.to_vec());
        }
    }
    #[test]
    fn structural_traits_match_derived_reference() {
        let mut samples = vec![atom(), gtrue(), gfalse()];
        for _ in 0..3 {
            let old = samples.clone();
            for (i, g) in old.iter().enumerate() {
                samples.push(binder(g.clone()));
                samples.push(Guarded::Conj(
                    vec![g.clone(), old[(i + 1) % old.len()].clone()].into(),
                ));
                samples.push(Guarded::Disj(vec![g.clone()].into()));
            }
        }
        let refs: Vec<_> = samples.iter().map(reference).collect();
        for (g, r) in samples.iter().zip(&refs) {
            assert_eq!(format!("{g:?}"), format!("{r:?}"));
            assert_eq!(format!("{g:#?}"), format!("{r:#?}"));
            let mut actual = Writes::default();
            let mut expected = Writes::default();
            g.hash(&mut actual);
            r.hash(&mut expected);
            assert_eq!(actual.0, expected.0);
            for (h, s) in samples.iter().zip(&refs) {
                assert_eq!(g.cmp(h), r.cmp(s));
                assert_eq!(g == h, r == s);
            }
        }
    }
    #[test]
    fn deep_branching_last_owner_drop() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let shared = binder(atom());
                let mut g = atom();
                for _ in 0..20_000 {
                    g = Guarded::Conj(vec![shared.clone(), g, atom()].into());
                }
                drop(g);
                assert_eq!(shared, binder(atom()));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn deep_guarded_operations_and_concurrent_last_owner_drop() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut g = atom();
                for _ in 0..20_000 {
                    g = binder(g);
                }
                assert_eq!(guarded_depth(&g), 20_002);
                let mapped = map_guarded_atoms(&g, &mut |_, atom| atom.clone());
                assert_eq!(g, mapped);
                assert_eq!(g.cmp(&mapped), std::cmp::Ordering::Equal);
                assert_eq!(
                    tamarin_utils::fx_hash_one(&g),
                    tamarin_utils::fx_hash_one(&mapped)
                );
                assert!(format!("{g:?}").len() > 20_000);
                drop(normalise_guarded_cow(&g));
                drop(gnot(&g));
                drop(simplify_guarded_with(&g, &|_| None));
                drop(to_induction_hypothesis(&g).unwrap());
                let x = LVar::new("x", LSort::Msg, 0);
                let subst = crate::tools::equation_store::LNSubst::from_map(
                    [(x, tamarin_term::lterm::pub_term("a"))].into(),
                );
                assert!(subst_guarded_cow(&g, &subst).is_some());
                drop(mapped);
                let barrier = Arc::new(std::sync::Barrier::new(2));
                let other = g.clone();
                let b = barrier.clone();
                let worker = std::thread::Builder::new()
                    .stack_size(256 * 1024)
                    .spawn(move || {
                        b.wait();
                        drop(other);
                    })
                    .unwrap();
                barrier.wait();
                drop(g);
                worker.join().unwrap();
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
