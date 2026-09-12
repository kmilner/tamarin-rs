//! Iterative structural operations for generic process owners.
use super::{Process, ProcessCombinator, SapicAction};
impl<A: Clone, V: Clone> Clone for Process<A, V> {
    fn clone(&self) -> Self {
        if let Self::Null(a) = self {
            return Self::Null(a.clone());
        }
        enum Task<'a, A, V> {
            Visit(&'a Process<A, V>),
            Action(SapicAction<V>, A),
            Comb(ProcessCombinator<V>, A),
        }
        let mut tasks = vec![Task::Visit(self)];
        let mut output = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Process::Null(a)) => output.push(Process::Null(a.clone())),
                Task::Visit(Process::Action(action, ann, body)) => {
                    tasks.push(Task::Action(action.clone(), ann.clone()));
                    tasks.push(Task::Visit(body));
                }
                Task::Visit(Process::Comb(comb, ann, l, r)) => {
                    tasks.push(Task::Comb(comb.clone(), ann.clone()));
                    tasks.push(Task::Visit(r));
                    tasks.push(Task::Visit(l));
                }
                Task::Action(action, ann) => {
                    let body = output.pop().unwrap();
                    output.push(Process::Action(action, ann, Box::new(body).into()));
                }
                Task::Comb(comb, ann) => {
                    let right = output.pop().unwrap();
                    let left = output.pop().unwrap();
                    output.push(Process::Comb(
                        comb,
                        ann,
                        Box::new(left).into(),
                        Box::new(right).into(),
                    ));
                }
            }
        }
        output.pop().unwrap()
    }
}
fn compare<A, V>(
    left: &Process<A, V>,
    right: &Process<A, V>,
    mut action: impl FnMut(&SapicAction<V>, &SapicAction<V>) -> Option<std::cmp::Ordering>,
    mut comb: impl FnMut(&ProcessCombinator<V>, &ProcessCombinator<V>) -> Option<std::cmp::Ordering>,
    mut ann: impl FnMut(&A, &A) -> Option<std::cmp::Ordering>,
) -> Option<std::cmp::Ordering> {
    use std::cmp::Ordering::Equal;
    fn tag<A, V>(p: &Process<A, V>) -> u8 {
        match p {
            Process::Null(_) => 0,
            Process::Comb(..) => 1,
            Process::Action(..) => 2,
        }
    }
    let mut current = (left, right);
    let mut pending = Vec::new();
    loop {
        let (l, r) = current;
        let order = tag(l).cmp(&tag(r));
        if order != Equal {
            return Some(order);
        }
        let order = match (l, r) {
            (Process::Null(a), Process::Null(b)) => ann(a, b),
            (Process::Action(a, h, p), Process::Action(b, j, q)) => {
                let o = action(a, b);
                if o != Some(Equal) {
                    return o;
                }
                let o = ann(h, j);
                if o != Some(Equal) {
                    return o;
                }
                current = (p, q);
                continue;
            }
            (Process::Comb(a, h, p, q), Process::Comb(b, j, r, s)) => {
                let o = comb(a, b);
                if o != Some(Equal) {
                    return o;
                }
                let o = ann(h, j);
                if o != Some(Equal) {
                    return o;
                }
                pending.push((&**q, &**s));
                current = (p, r);
                continue;
            }
            _ => unreachable!(),
        };
        if order != Some(Equal) {
            return order;
        }
        let Some(next) = pending.pop() else {
            return Some(Equal);
        };
        current = next;
    }
}
impl<A: PartialEq, V: PartialEq> PartialEq for Process<A, V> {
    fn eq(&self, other: &Self) -> bool {
        use std::cmp::Ordering::{Equal, Less};
        compare(
            self,
            other,
            |a, b| Some(if a == b { Equal } else { Less }),
            |a, b| Some(if a == b { Equal } else { Less }),
            |a, b| Some(if a == b { Equal } else { Less }),
        ) == Some(Equal)
    }
}
impl<A: Eq, V: Eq> Eq for Process<A, V> {}
impl<A: PartialOrd, V: PartialOrd> PartialOrd for Process<A, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        compare(
            self,
            other,
            PartialOrd::partial_cmp,
            PartialOrd::partial_cmp,
            PartialOrd::partial_cmp,
        )
    }
}
impl<A: Ord, V: Ord> Ord for Process<A, V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        compare(
            self,
            other,
            |a, b| Some(a.cmp(b)),
            |a, b| Some(a.cmp(b)),
            |a, b| Some(a.cmp(b)),
        )
        .unwrap()
    }
}
impl<A: std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for Process<A, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            return tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Process::Null(a) => f.debug_tuple("Null").field(a).finish(),
                Process::Action(a, h, p) => {
                    f.debug_tuple("Action").field(a).field(h).field(p).finish()
                }
                Process::Comb(c, h, p, q) => f
                    .debug_tuple("Comb")
                    .field(c)
                    .field(h)
                    .field(p)
                    .field(q)
                    .finish(),
            });
        }
        enum Task<'a, A, V> {
            Node(&'a Process<A, V>),
            Text(&'static str),
        }
        let mut pending = vec![Task::Node(self)];
        while let Some(task) = pending.pop() {
            match task {
                Task::Text(s) => f.write_str(s)?,
                Task::Node(p) => match p {
                    Process::Null(a) => {
                        f.debug_tuple("Null").field(a).finish()?;
                    }
                    Process::Action(a, h, p) => {
                        f.write_str("Action(")?;
                        std::fmt::Debug::fmt(a, f)?;
                        f.write_str(", ")?;
                        std::fmt::Debug::fmt(h, f)?;
                        f.write_str(", ")?;
                        pending.push(Task::Text(")"));
                        pending.push(Task::Node(p));
                    }
                    Process::Comb(c, h, p, q) => {
                        f.write_str("Comb(")?;
                        std::fmt::Debug::fmt(c, f)?;
                        f.write_str(", ")?;
                        std::fmt::Debug::fmt(h, f)?;
                        f.write_str(", ")?;
                        pending.push(Task::Text(")"));
                        pending.push(Task::Node(q));
                        pending.push(Task::Text(", "));
                        pending.push(Task::Node(p));
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
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Reference {
        Null(u8),
        Comb(ProcessCombinator<u8>, u8, Box<Reference>, Box<Reference>),
        Action(SapicAction<u8>, u8, Box<Reference>),
    }
    fn reference(p: &Process<u8, u8>) -> Reference {
        match p {
            Process::Null(a) => Reference::Null(*a),
            Process::Action(a, h, p) => Reference::Action(a.clone(), *h, Box::new(reference(p))),
            Process::Comb(c, h, p, q) => Reference::Comb(
                c.clone(),
                *h,
                Box::new(reference(p)),
                Box::new(reference(q)),
            ),
        }
    }
    #[test]
    fn structural_traits_match_derived_reference() {
        let mut samples = vec![Process::Null(0), Process::Null(1)];
        for i in 0..12 {
            let p = samples[i].clone();
            samples.push(Process::Action(
                SapicAction::New(i as u8),
                i as u8,
                Box::new(p.clone()).into(),
            ));
            samples.push(Process::Comb(
                ProcessCombinator::Parallel,
                i as u8,
                Box::new(p).into(),
                Box::new(Process::Null(0)).into(),
            ));
        }
        for p in &samples {
            let r = reference(p);
            assert_eq!(format!("{p:?}"), format!("{r:?}"));
            assert_eq!(format!("{p:#?}"), format!("{r:#?}"));
            for q in &samples {
                assert_eq!(p.cmp(q), r.cmp(&reference(q)));
            }
        }
        let p: Process<f64, u8> = Process::Action(
            SapicAction::Rep,
            f64::NAN,
            Box::new(Process::Null(0.0)).into(),
        );
        assert_ne!(p, p);
        assert_eq!(p.partial_cmp(&p), None);
    }
    #[test]
    fn deep_process_lifecycle_uses_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut p: Process<(), u8> = Process::Null(());
                for _ in 0..100_000 {
                    p = Process::Action(SapicAction::Rep, (), Box::new(p).into());
                }
                let cloned = p.clone();
                assert_eq!(p, cloned);
                assert_eq!(p.cmp(&cloned), std::cmp::Ordering::Equal);
                assert!(format!("{p:?}").len() > 100_000);
                drop((p, cloned));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
