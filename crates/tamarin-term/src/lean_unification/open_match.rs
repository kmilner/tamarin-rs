//! Match trees built from free, C and AC symbols against rigid subject occurrences.
//! The selector keeps positions distinct. The partition kernel shares one row
//! per actual variable, including variables also bound in a constructor.
use super::{
    flat_rows, initialize, partition_work, subsort, Error, MatchRows, Outcome, LEAN_THREAD,
};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{sort_of_lterm, LNTerm, LVar};
use crate::maude_types::sort_of_name;
use crate::term::{f_app_ac, map_lits, Term};
use crate::vterm::Lit;
use std::ffi::c_void;
use std::{borrow::Cow, collections::BTreeSet, rc::Rc};

unsafe extern "C" {
    fn tamarin_lean_open_match_select(rigid: u64, subject: u64) -> *mut c_void;
    fn tamarin_lean_collector_possible(
        occurrences: *const u64,
        occurrences_len: usize,
        factors: *const u64,
        factors_len: usize,
    ) -> u8;
}

type Arm = Vec<(LVar, LNTerm)>;

// Canonical AC applications are flat at their own head and sorted. Each
// child must itself be canonical before its full identity can be interned.
fn canonical_tree(t: &LNTerm, ground: bool) -> Option<bool> {
    let (args, mut sorted) = match t {
        Term::Lit(Lit::Con(_)) => return Some(true),
        Term::Lit(Lit::Var(_)) => return (!ground).then_some(true),
        Term::App(FunSym::NoEq(f), args) if f.arity == args.len() => (args, true),
        Term::App(FunSym::C(_), args) if args.len() == 2 => (args, args[0] <= args[1]),
        Term::App(f @ FunSym::Ac(_), args) if args.len() >= 2 => (
            args,
            args.is_sorted() && !args.iter().any(|a| matches!(a, Term::App(g, _) if g == f)),
        ),
        _ => return None,
    };
    for arg in args.iter() {
        sorted &= canonical_tree(arg, ground)?;
    }
    Some(sorted)
}

pub(super) fn ground_form(t: &LNTerm) -> Option<Cow<'_, LNTerm>> {
    Some(if canonical_tree(t, true)? {
        Cow::Borrowed(t)
    } else {
        Cow::Owned(map_lits(t, &mut |lit| *lit))
    })
}

pub(super) fn prepare(
    symbol: AcSym,
    factors: &[LNTerm],
    ground: bool,
) -> Option<Cow<'_, [LNTerm]>> {
    let head = FunSym::Ac(symbol);
    let mut ready = true;
    for t in factors {
        // The top-level order of factors is irrelevant to the selector, but
        // a raw child at the same AC head must contribute all its occurrences.
        ready &= canonical_tree(t, ground)? && !matches!(t, Term::App(f, _) if *f == head);
    }
    Some(if ready {
        Cow::Borrowed(factors)
    } else {
        let mut flat = Vec::with_capacity(factors.len());
        for t in factors {
            match map_lits(t, &mut |lit| *lit) {
                Term::App(f, xs) if f == head => flat.extend(xs.iter().cloned()),
                atom => flat.push(atom),
            }
        }
        Cow::Owned(flat)
    })
}

fn tree_nodes(t: &LNTerm) -> Option<usize> {
    match t {
        Term::Lit(_) => Some(1),
        Term::App(_, args) => args
            .iter()
            .try_fold(1usize, |n, t| n.checked_add(tree_nodes(t)?)),
    }
}

fn bind(v: LVar, t: &LNTerm, arm: &mut Arm) -> bool {
    if !subsort(sort_of_lterm(t, sort_of_name), v.sort) {
        return false;
    }
    if let Some((_, old)) = arm.iter().find(|(key, _)| *key == v) {
        // Both the selected subtrees and the products of residual factors
        // are canonical subject terms, including products bound at nested heads.
        return old == t;
    }
    arm.push((v, t.clone()));
    true
}

/// In a flat AC match every nonvariable pattern factor consumes exactly one
/// subject factor with the same head. Return forced pairs to the caller while
/// checking each head's available multiplicity. Subject variables stay rigid.
pub(super) fn align_rigid_factors<'a>(
    pattern: &'a [LNTerm],
    subject: &'a [LNTerm],
    mut compare: impl FnMut(&'a LNTerm, &'a LNTerm) -> bool,
) -> bool {
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum Head {
        Atom(crate::lterm::Name),
        App(FunSym),
    }
    let head = |t: &LNTerm| match t {
        Term::Lit(Lit::Var(_)) => None,
        Term::Lit(Lit::Con(c)) => Some(Head::Atom(*c)),
        Term::App(f, _) => Some(Head::App(*f)),
    };
    if pattern.iter().all(|t| head(t).is_none()) {
        return true;
    }
    let mut buckets = rustc_hash::FxHashMap::default();
    for s in subject {
        if let Some(h) = head(s) {
            let (count, only) = buckets.entry(h).or_insert((0usize, Some(s)));
            *count += 1;
            if *count > 1 {
                *only = None;
            }
        }
    }
    for p in pattern {
        let Some(h) = head(p) else { continue };
        let Some((remaining, only)) = buckets.get_mut(&h) else {
            return false;
        };
        if *remaining == 0 || only.is_some_and(|s| !compare(p, s)) {
            return false;
        }
        *remaining -= 1;
    }
    true
}

struct Collectors {
    symbol: AcSym,
    keys: IdentityTable<LVar>,
    occurrences: Vec<u64>,
}

impl Collectors {
    // Subject variables are rigid leaves. Equal canonical terms receive the same
    // numeric ID, so counts preserve multiplicity even for repeated variables.
    fn encode_remainder<'a>(
        rest: &[&'a LNTerm],
    ) -> Result<(IdentityTable<&'a LNTerm>, Vec<u64>), Error> {
        let mut factors = IdentityTable::default();
        let rhs = rest
            .iter()
            .map(|&t| factors.intern(t).ok_or(Error::InvalidStatus(255)))
            .collect::<Result<_, _>>()?;
        Ok((factors, rhs))
    }

    fn refuted(&self, rhs: &[u64]) -> Result<bool, Error> {
        // SAFETY: both ID slices live through the synchronous shim call.
        match unsafe {
            tamarin_lean_collector_possible(
                self.occurrences.as_ptr(),
                self.occurrences.len(),
                rhs.as_ptr(),
                rhs.len(),
            )
        } {
            0 => Ok(true),
            1 => Ok(false),
            tag => Err(Error::InvalidStatus(tag)),
        }
    }

    fn extend<'a>(
        &self,
        rest: &[&LNTerm],
        mut arm: Arm,
        pending: &[Task<'a>],
        search: &mut Search<'a, '_>,
    ) -> Result<bool, Error> {
        if self.occurrences.len() == 1 {
            let image = f_app_ac(self.symbol, rest.iter().map(|&t| t.clone()).collect());
            if bind(self.keys.values()[0], &image, &mut arm) {
                return Ok(search.resume(pending, arm));
            }
            return Ok(true);
        }
        // Earlier coordinates may already have fixed collectors in this AC
        // equation. Remove their exact flattened images before partitioning.
        // Subject variables in those captures remain rigid.
        if self
            .keys
            .values()
            .iter()
            .any(|key| arm.iter().any(|(v, _)| v == key))
        {
            let mut fixed = Vec::new();
            let mut open = Collectors {
                symbol: self.symbol,
                keys: IdentityTable::default(),
                occurrences: Vec::new(),
            };
            for &index in &self.occurrences {
                let key = self.keys.get(index).ok_or(Error::InvalidStatus(255))?;
                if let Some((_, image)) = arm.iter().find(|(v, _)| *v == key) {
                    let pieces = match image {
                        Term::App(FunSym::Ac(head), xs) if *head == self.symbol => xs.as_ref(),
                        atom => std::slice::from_ref(atom),
                    };
                    if pieces.len() > rest.len() - fixed.len() {
                        return Ok(true);
                    }
                    fixed.extend(pieces);
                } else {
                    open.occurrences
                        .push(open.keys.intern(key).ok_or(Error::InvalidStatus(255))?);
                }
            }
            let (missing, remaining) =
                super::common_children::residual_refs(fixed, rest.iter().copied())?;
            if !missing.is_empty() || remaining.len() < open.occurrences.len() {
                return Ok(true);
            }
            if open.occurrences.is_empty() {
                return Ok(!remaining.is_empty() || search.resume(pending, arm));
            }
            return open.extend(&remaining, arm.clone(), pending, search);
        }
        let (factors, rhs) = Self::encode_remainder(rest)?;
        if self.keys.len() < self.occurrences.len() && self.refuted(&rhs)? {
            return Ok(true);
        }
        let Some(left) = partition_work(self.occurrences.len(), self.keys.len(), &rhs)
            .and_then(|work| search.budget.checked_sub(work))
        else {
            return Ok(false);
        };
        *search.budget = left;
        let packet = MatchRows::new(flat_rows(self.keys.len(), &self.occurrences, &[], &rhs))?;
        let mut row = vec![0; rhs.len()];
        'branches: for i in 0..packet.count() {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            if packet.rows(i) != self.keys.len() {
                return Err(Error::InvalidStatus(255));
            }
            let mut bindings = arm.clone();
            for (j, &key) in self.keys.values().iter().enumerate() {
                let size = packet.copy_row(i, j, &mut row)?;
                let image = row[..size]
                    .iter()
                    .map(|&id| factors.get(id).cloned().ok_or(Error::InvalidSubject(id)))
                    .collect::<Result<Vec<_>, _>>()?;
                if !bind(key, &f_app_ac(self.symbol, image), &mut bindings) {
                    continue 'branches;
                }
            }
            if !search.resume(pending, bindings) {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

// At each AC node cancel closed siblings before selecting the open rigid
// factors. The remaining arrays refer to canonical operands of the original
// input, whose lifetimes extend through every pending continuation.
struct AcProblem<'a> {
    rigid: Vec<&'a LNTerm>,
    collectors: Collectors,
    subject: Vec<&'a LNTerm>,
}

impl<'a> AcProblem<'a> {
    fn new(
        symbol: AcSym,
        pattern: &'a [LNTerm],
        subject: &'a [LNTerm],
    ) -> Result<Option<Self>, Error> {
        // With no unit every pattern occurrence consumes at least one factor.
        if pattern.len() > subject.len() {
            return Ok(None);
        }
        let mut fixed = Vec::new();
        let mut rigid = Vec::new();
        let mut collectors = Collectors {
            symbol,
            keys: IdentityTable::default(),
            occurrences: Vec::new(),
        };
        for t in pattern {
            if let Term::Lit(Lit::Var(v)) = t {
                collectors.occurrences.push(
                    collectors
                        .keys
                        .intern(*v)
                        .ok_or(Error::InvalidStatus(255))?,
                );
            } else if crate::vterm::is_ground_vterm(t) {
                fixed.push(t);
            } else {
                rigid.push(t);
            }
        }
        let subject = if fixed.is_empty() {
            subject.iter().collect()
        } else {
            let (missing, rest) = super::common_children::residual_refs(fixed, subject)?;
            if !missing.is_empty() {
                return Ok(None);
            }
            rest
        };
        // Every open nonvariable factor has a head distinct from this AC head
        // after flattening, and must consume exactly one subject occurrence.
        if collectors.occurrences.is_empty() && rigid.len() != subject.len() {
            return Ok(None);
        }
        Ok(Some(Self {
            rigid,
            collectors,
            subject,
        }))
    }
}

// A selected AC row contributes child equations followed by a partition of
// its unused occurrences. Sharing the immutable remainder makes cloning a
// pending continuation independent of the number of factors in that row.
#[derive(Clone)]
enum Task<'a> {
    Pair(&'a LNTerm, &'a LNTerm),
    Remainder(Rc<Collectors>, Rc<[&'a LNTerm]>),
}

struct Search<'a, 'b> {
    work: Vec<(Vec<Task<'a>>, Arm)>,
    answers: BTreeSet<Arm>,
    cost: usize,
    budget: &'b mut usize,
}

impl<'a> Search<'a, '_> {
    fn charge_branch(&mut self) -> bool {
        let Some(left) = self.budget.checked_sub(self.cost) else {
            return false;
        };
        *self.budget = left;
        true
    }

    fn record(&mut self, mut arm: Arm) {
        arm.sort();
        self.answers.insert(arm);
    }

    fn resume(&mut self, pending: &[Task<'a>], arm: Arm) -> bool {
        if pending.is_empty() {
            self.record(arm);
        } else {
            if !self.charge_branch() {
                return false;
            }
            self.work.push((pending.to_vec(), arm));
        }
        true
    }

    fn select(
        &mut self,
        problem: AcProblem<'a>,
        pending: &[Task<'a>],
        arm: Arm,
    ) -> Result<bool, Error> {
        let AcProblem {
            rigid,
            collectors,
            subject,
        } = problem;
        if rigid.is_empty() {
            match collectors.occurrences.len() {
                0 => return Ok(self.resume(pending, arm)),
                1 => return collectors.extend(&subject, arm, pending, self),
                _ => {}
            }
        }
        let collectors = Rc::new(collectors);
        // SAFETY: the shim returns null on deferral and otherwise transfers
        // one reference containing selection rows under a single outer array.
        let raw =
            unsafe { tamarin_lean_open_match_select(rigid.len() as u64, subject.len() as u64) };
        if raw.is_null() {
            // With no structural factors left, the subject is the exact
            // remainder. A certified refutation can finish this branch even
            // when the selector declines. Every live partition still defers.
            if rigid.is_empty() && collectors.keys.len() < collectors.occurrences.len() {
                let (_, rhs) = Collectors::encode_remainder(&subject)?;
                return collectors.refuted(&rhs);
            }
            return Ok(false);
        }
        let selections = MatchRows::new(raw)?;
        if selections.count() != 1 {
            return Err(Error::InvalidStatus(255));
        }
        let count = selections.rows(0);
        if count == 0 {
            return Ok(true);
        }
        let mut row = vec![0; subject.len()];
        for i in 0..count {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            if !self.charge_branch() {
                return Ok(false);
            }
            let len = selections.copy_row(0, i, &mut row)?;
            if len != subject.len() || len < rigid.len() {
                return Err(Error::InvalidStatus(255));
            }
            let get = |&id: &u64| {
                subject
                    .get(id as usize)
                    .copied()
                    .ok_or(Error::InvalidSubject(id))
            };
            let (selected, rest) = row.split_at(rigid.len());
            let mut next = pending.to_vec();
            if !collectors.occurrences.is_empty() {
                let rest = rest.iter().map(get).collect::<Result<Rc<[_]>, _>>()?;
                next.push(Task::Remainder(Rc::clone(&collectors), rest));
            }
            for (p, id) in rigid.iter().zip(selected).rev() {
                next.push(Task::Pair(p, get(id)?));
            }
            self.work.push((next, arm.clone()));
        }
        Ok(true)
    }

    fn run(&mut self) -> Result<bool, Error> {
        'branch: while let Some((mut pending, mut arm)) = self.work.pop() {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            while let Some(task) = pending.pop() {
                let (p, s) = match task {
                    Task::Pair(p, s) => (p, s),
                    Task::Remainder(collectors, rest) => {
                        if !collectors.extend(&rest, arm, &pending, self)? {
                            return Ok(false);
                        }
                        continue 'branch;
                    }
                };
                match (p, s) {
                    (Term::Lit(Lit::Var(v)), _) if bind(*v, s, &mut arm) => {}
                    (Term::Lit(Lit::Con(a)), Term::Lit(Lit::Con(b))) if a == b => {}
                    (Term::App(FunSym::NoEq(f), ps), Term::App(FunSym::NoEq(g), ss)) if f == g => {
                        pending.extend(
                            ps.iter()
                                .zip(ss.iter())
                                .rev()
                                .map(|(p, s)| Task::Pair(p, s)),
                        );
                    }
                    (Term::App(FunSym::C(f), ps), Term::App(FunSym::C(g), ss)) if f == g => {
                        let (a, b, c, d) = (&ps[0], &ps[1], &ss[0], &ss[1]);
                        match super::commutative::match_orientations([a, b, c, d])? {
                            0 => continue 'branch,
                            1 => pending.extend([Task::Pair(b, d), Task::Pair(a, c)]),
                            2 => pending.extend([Task::Pair(b, c), Task::Pair(a, d)]),
                            3 => {
                                if !self.charge_branch() {
                                    return Ok(false);
                                }
                                let mut crossed = pending.clone();
                                crossed.extend([Task::Pair(b, c), Task::Pair(a, d)]);
                                self.work.push((crossed, arm.clone()));
                                pending.extend([Task::Pair(b, d), Task::Pair(a, c)]);
                            }
                            mask => return Err(Error::InvalidStatus(mask)),
                        }
                    }
                    (Term::App(FunSym::Ac(f), ps), Term::App(FunSym::Ac(g), ss)) if f == g => {
                        let Some(problem) = AcProblem::new(*f, ps, ss)? else {
                            continue 'branch;
                        };
                        if !self.select(problem, &pending, arm)? {
                            return Ok(false);
                        }
                        continue 'branch;
                    }
                    _ => continue 'branch,
                }
            }
            self.record(arm);
        }
        Ok(true)
    }
}

pub(super) fn component(
    symbol: AcSym,
    pattern: &[LNTerm],
    subject: &[LNTerm],
    budget: &mut usize,
) -> Result<Outcome, Error> {
    let Some(problem) = AcProblem::new(symbol, pattern, subject)? else {
        return Ok(Outcome::Complete(Vec::new()));
    };
    // Charge the size of the live root problem per branch to bound both the
    // number of continuations and the work copied into them.
    let Some(cost) = problem
        .rigid
        .iter()
        .chain(&problem.subject)
        .try_fold(problem.collectors.occurrences.len(), |n, t| {
            n.checked_add(tree_nodes(t)?)
        })
    else {
        return Ok(Outcome::Unsupported);
    };
    initialize()?;
    LEAN_THREAD.with(|_| {
        let mut search = Search {
            work: Vec::new(),
            answers: BTreeSet::new(),
            cost,
            budget,
        };
        if !search.select(problem, &[], Arm::new())? || !search.run()? {
            return Ok(Outcome::Unsupported);
        }
        Ok(Outcome::Complete(search.answers.into_iter().collect()))
    })
}

/// Match one canonical pattern against a canonical subject with rigid variables.
/// Rule candidates and subgroups in a reduction consume the same search budget.
pub(super) fn root(
    pattern: &LNTerm,
    subject: &LNTerm,
    budget: &mut usize,
) -> Result<Outcome, Error> {
    let Some(cost) = tree_nodes(pattern).and_then(|n| n.checked_add(tree_nodes(subject)?)) else {
        return Ok(Outcome::Unsupported);
    };
    search(vec![Task::Pair(pattern, subject)], Arm::new(), cost, budget)
}

/// Match a conjunction against canonical rigid subjects. Every continuation
/// carries the initial forced images alongside all later variable bindings.
pub(super) fn with_captures(
    equations: &[crate::rewriting::Equal<LNTerm>],
    captures: Arm,
) -> Result<Outcome, Error> {
    with_captures_budget(equations, captures, &mut 100_000)
}

pub(super) fn with_captures_budget(
    equations: &[crate::rewriting::Equal<LNTerm>],
    captures: Arm,
    budget: &mut usize,
) -> Result<Outcome, Error> {
    let terms = equations.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]);
    let Some(cost) = terms
        .chain(captures.iter().map(|(_, t)| t))
        .try_fold(0usize, |n, t| n.checked_add(tree_nodes(t)?))
    else {
        return Ok(Outcome::Unsupported);
    };
    let tasks = equations
        .iter()
        .rev()
        .map(|eq| Task::Pair(&eq.lhs, &eq.rhs))
        .collect();
    search(tasks, captures, cost, budget)
}

fn search(
    tasks: Vec<Task<'_>>,
    captures: Arm,
    cost: usize,
    budget: &mut usize,
) -> Result<Outcome, Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        let mut search = Search {
            work: Vec::new(),
            answers: BTreeSet::new(),
            cost,
            budget,
        };
        if !search.charge_branch() {
            return Ok(Outcome::Unsupported);
        }
        search.work.push((tasks, captures));
        if !search.run()? {
            return Ok(Outcome::Unsupported);
        }
        Ok(Outcome::Complete(search.answers.into_iter().collect()))
    })
}

#[cfg(test)]
mod tests {
    use super::align_rigid_factors;
    use crate::builtin::{hash, msg_var, pair};
    use crate::lterm::pub_term;

    #[test]
    fn already_bound_collectors_consume_their_full_bag_at_each_occurrence() {
        use super::{with_captures, Outcome};
        use crate::builtin::mult;
        use crate::lterm::{LSort, LVar};
        use crate::rewriting::Equal;
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("x", LSort::Msg, 1);
        let xy = mult(msg_var("x", 0), mult(msg_var("x", 0), msg_var("x", 1)));
        let image = mult(pub_term("a"), pub_term("b"));
        let target = mult(image.clone(), mult(image.clone(), pub_term("c")));
        let eq = |t| Equal {
            lhs: xy.clone(),
            rhs: t,
        };
        let seed = vec![(x, image.clone())];
        assert_eq!(
            with_captures(&[eq(target)], seed.clone()).unwrap(),
            Outcome::Complete(vec![vec![(x, image.clone()), (y, pub_term("c"))]])
        );
        assert_eq!(
            with_captures(&[eq(mult(image, pub_term("c")))], seed).unwrap(),
            Outcome::Complete(vec![])
        );
    }

    #[test]
    fn forced_ac_factors_preserve_ambiguous_occurrences() {
        let x = msg_var("x", 0);
        let a = pub_term("a");
        let px = pair(x.clone(), x.clone());
        let pa = pair(a.clone(), a.clone());
        let hx = hash(x);
        let ha = hash(a);
        let subject = [pa.clone(), ha.clone(), ha.clone()];
        let mut forced = Vec::new();
        let pattern = [hx.clone(), px.clone(), hx.clone()];
        assert!(align_rigid_factors(&pattern, &subject, |p, s| {
            forced.push((p, s));
            true
        }));
        assert_eq!(forced, [(&px, &pa)]);
        assert!(!align_rigid_factors(
            &[hx.clone(), hx.clone(), hx],
            &subject,
            |_, _| true
        ));
    }
}
