// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Term.Raw` from `lib/term/src/Term/Term/Raw.hs`.
//!
//! The core term datatype with its smart constructors and view types.
//! AC operators (Mult, Xor, Union, NatPlus, and user-defined AC symbols)
//! are normalised by [`f_app`]: arguments are flattened across nested
//! same-symbol applications and sorted into a canonical order.

use crate::function_symbols::{AcFctSym, AcSym, CSym, FunSym, NoEqSym, EMAP_SYM_STRING};
use std::borrow::Cow;
use std::sync::Arc;

/// A term over literal type `A`. Construct via [`lit`] / [`f_app`] /
/// [`f_app_no_eq`] / [`f_app_list`] — never via the variants directly,
/// because [`Term::App`] expects AC-normalised argument lists.
///
/// Children of [`Term::App`] are held in [`TermArgs`] so that cloning a
/// `Term` is O(1) (one atomic refcount bump) instead of a recursive deep
/// clone.  This mirrors GHC's structural sharing of term subtrees: a
/// `Term` in Haskell is a pointer-sized value shared across many sites by
/// reference, never deep-copied.  It keeps the solver's hottest allocation
/// path (`subst_system_once → Goal::clone → Fact::clone → Term::clone`)
/// off the allocator.
///
/// Reading (`args.iter()`, `args.len()`, `args[i]`, `&args[..]`) works
/// because `TermArgs` derefs to `[_]`. Construction sites convert via
/// `vec.into()`; destructure-and-consume patterns
/// use `args.iter().cloned()` (each child clone is itself O(1)).
#[derive(Clone)]
pub enum Term<A> {
    Lit(A),
    App(FunSym, TermArgs<A>),
}

/// Shared immutable arguments with iterative last-owner destruction.
/// The sized Arc payload lets `into_inner` transfer ownership of its children
/// to a worklist, including when several threads release shared terms at once.
pub struct TermArgs<A>(Arc<OwnedArgs<A>>);

struct OwnedArgs<A>(Box<[Term<A>]>);

impl<A> Clone for TermArgs<A> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<A> From<Vec<Term<A>>> for TermArgs<A> {
    #[inline]
    fn from(args: Vec<Term<A>>) -> Self {
        Self(Arc::new(OwnedArgs(args.into_boxed_slice())))
    }
}

impl<A> FromIterator<Term<A>> for TermArgs<A> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = Term<A>>>(iter: I) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl<A> std::ops::Deref for TermArgs<A> {
    type Target = [Term<A>];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0 .0
    }
}

impl<A> AsRef<[Term<A>]> for TermArgs<A> {
    #[inline]
    fn as_ref(&self) -> &[Term<A>] {
        self
    }
}

impl<A: std::fmt::Debug> std::fmt::Debug for TermArgs<A> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<A> TermArgs<A> {
    #[inline]
    fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<A> Drop for OwnedArgs<A> {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.0).into_vec();
        pending.reverse();
        while let Some(term) = pending.pop() {
            if let Term::App(_, args) = term {
                // Unlike try_unwrap followed by dropping Err, into_inner
                // cannot trigger recursive last-owner destruction in a race.
                if let Some(children) = Arc::into_inner(args.0) {
                    // Its only owned field moves to the worklist. Suppress the
                    // now-empty payload's destructor instead of re-entering it.
                    let mut children = std::mem::ManuallyDrop::new(children);
                    pending.extend(std::mem::take(&mut children.0).into_vec().into_iter().rev());
                }
            }
        }
    }
}

// Hand-written `Eq`/`Ord` with a structural-sharing fast-path.  `Term::App`
// children live in shared argument storage, so two terms cloned from a common source
// (pervasive in the proof search — substitution shares subterms) point at the
// SAME slice; `Arc::ptr_eq` then settles equality/ordering in O(1) instead of a
// deep recursive walk.  The std `Ord for Arc` does NOT short-circuit on pointer
// identity (only `PartialEq` does), which is why `cmp`/`partial_cmp` are
// hand-written here.  Correctness: `Arc::ptr_eq ⇒ true` means the same
// allocation ⇒ identical contents, so the answer equals the purely
// content-based one; on a pointer mismatch we fall back to the full structural
// comparison.  Variant order (Lit < App) and field order match the derived
// impls exactly, which is HS `data Term a = LIT a | FAPP FunSym [Term a]`
// with a derived `Eq`/`Ord` (Term/Term/Raw.hs:73-75).
impl<A: PartialEq> PartialEq for Term<A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let mut slices = (std::slice::from_ref(self), std::slice::from_ref(other));
        let mut pending = Vec::new();
        loop {
            while let Some((left, rest_left)) = slices.0.split_first() {
                let (right, rest_right) = slices.1.split_first().unwrap();
                slices = (rest_left, rest_right);
                match (left, right) {
                    (Term::Lit(a), Term::Lit(b)) if a == b => {}
                    (Term::App(s1, a1), Term::App(s2, a2)) if s1 == s2 => {
                        if !a1.ptr_eq(a2) {
                            if a1.len() != a2.len() {
                                return false;
                            }
                            // Flat arguments need no worklist. Suspend siblings
                            // only when descending into a nested application.
                            if !rest_left.is_empty() {
                                pending.push(slices);
                            }
                            slices = (a1, a2);
                        }
                    }
                    _ => return false,
                }
            }
            let Some(next) = pending.pop() else {
                return true;
            };
            slices = next;
        }
    }
}
impl<A: Eq> Eq for Term<A> {}

// Walk sibling slices lexicographically. Only branches need a continuation;
// literals, shared applications and unary chains allocate no worklist storage.
fn compare_terms<A>(
    left: &Term<A>,
    right: &Term<A>,
    cmp: impl Fn(&A, &A) -> Option<std::cmp::Ordering>,
) -> Option<std::cmp::Ordering> {
    use std::cmp::Ordering;
    let mut slices = (std::slice::from_ref(left), std::slice::from_ref(right));
    let mut pending = Vec::new();
    loop {
        match (slices.0.split_first(), slices.1.split_first()) {
            (Some((a, rest_a)), Some((b, rest_b))) => {
                slices = (rest_a, rest_b);
                let order = match (a, b) {
                    (Term::Lit(a), Term::Lit(b)) => cmp(a, b)?,
                    (Term::Lit(_), Term::App(..)) => Ordering::Less,
                    (Term::App(..), Term::Lit(_)) => Ordering::Greater,
                    (Term::App(s1, a1), Term::App(s2, a2)) => {
                        let order = s1.cmp(s2);
                        if order == Ordering::Equal && !a1.ptr_eq(a2) {
                            if !rest_a.is_empty() || !rest_b.is_empty() {
                                pending.push(slices);
                            }
                            slices = (a1, a2);
                            continue;
                        }
                        order
                    }
                };
                if order != Ordering::Equal {
                    return Some(order);
                }
            }
            _ => {
                let order = slices.0.len().cmp(&slices.1.len());
                if order != Ordering::Equal {
                    return Some(order);
                }
                let Some(next) = pending.pop() else {
                    return Some(Ordering::Equal);
                };
                slices = next;
            }
        }
        if slices.0.is_empty() && slices.1.is_empty() && pending.is_empty() {
            return Some(Ordering::Equal);
        }
    }
}

impl<A: Ord> Ord for Term<A> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        compare_terms(self, other, |a, b| Some(a.cmp(b))).expect("total order")
    }
}
impl<A: PartialOrd> PartialOrd for Term<A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        compare_terms(self, other, A::partial_cmp)
    }
}
// Hand-written `Hash` to accompany the manual ptr-fast-path `PartialEq`/`Ord`
// above, satisfying `clippy::derived_hash_with_manual_eq` (a correctness lint
// guarding `a == b ⇒ hash(a) == hash(b)`).  This hash is purely content-based —
// `App` always hashes its symbol and children, never the `Arc` identity — so it
// agrees with the content-based `Eq`.  No `HashMap`/`FastSet` keyed on `Term`
// has an iteration order that reaches the prover output (the port is byte-
// deterministic), so the concrete hash value is output-irrelevant.
impl<A: std::hash::Hash> std::hash::Hash for Term<A> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut nodes = std::slice::from_ref(self).iter();
        let mut pending = Vec::new();
        loop {
            while let Some(node) = nodes.next() {
                match node {
                    Term::Lit(a) => {
                        0u8.hash(state);
                        a.hash(state);
                    }
                    Term::App(s, args) => {
                        1u8.hash(state);
                        s.hash(state);
                        args.len().hash(state);
                        if !args.is_empty() {
                            if !nodes.as_slice().is_empty() {
                                pending.push(nodes);
                            }
                            nodes = args.iter();
                            break;
                        }
                    }
                }
            }
            if nodes.as_slice().is_empty() {
                let Some(next) = pending.pop() else { return };
                nodes = next;
            }
        }
    }
}

impl<A: std::fmt::Debug> std::fmt::Debug for Term<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Term::Lit(a) = self {
            return f.debug_tuple("Lit").field(a).finish();
        }
        if f.alternate() {
            // Keep the standard formatter's indentation and all caller flags.
            // Alternate output is quadratic in depth; this uncommon path uses
            // stack growth rather than duplicating Rust's formatting engine.
            return tamarin_utils::stack::ensure_sufficient_stack(|| match self {
                Term::Lit(a) => f.debug_tuple("Lit").field(a).finish(),
                Term::App(s, args) => f.debug_tuple("App").field(s).field(args).finish(),
            });
        }
        enum Task<'a, A> {
            Node(&'a Term<A>),
            Args(std::slice::Iter<'a, Term<A>>, bool),
        }
        let mut pending = vec![Task::Node(self)];
        while let Some(task) = pending.pop() {
            match task {
                Task::Node(Term::Lit(a)) => {
                    f.debug_tuple("Lit").field(a).finish()?;
                }
                Task::Node(Term::App(s, args)) => {
                    f.write_str("App(")?;
                    std::fmt::Debug::fmt(s, f)?;
                    f.write_str(", [")?;
                    pending.push(Task::Args(args.iter(), false));
                }
                Task::Args(mut args, separator) => {
                    if let Some(arg) = args.next() {
                        if separator {
                            f.write_str(", ")?;
                        }
                        pending.push(Task::Args(args, true));
                        pending.push(Task::Node(arg));
                    } else {
                        f.write_str("])")?;
                    }
                }
            }
        }
        Ok(())
    }
}

/// Preorder traversal shared by read-only queries. `Continue(false)` prunes a
/// matched subtree; `Break` short-circuits without visiting later siblings.
pub fn walk_terms<A, B>(
    roots: &[Term<A>],
    mut visit: impl FnMut(&Term<A>) -> std::ops::ControlFlow<B, bool>,
) -> std::ops::ControlFlow<B> {
    use std::ops::ControlFlow;
    let mut current = roots.iter();
    let mut pending = Vec::new();
    loop {
        while let Some(node) = current.next() {
            if visit(node)?
                && let Term::App(_, args) = node
                && !args.is_empty()
            {
                if !current.as_slice().is_empty() {
                    pending.push(current);
                }
                current = args.iter();
            }
        }
        let Some(next) = pending.pop() else {
            return ControlFlow::Continue(());
        };
        current = next;
    }
}

impl<A> Term<A> {
    /// Visit literals left to right without rebuilding the term.
    pub fn for_each_lit(&self, mut f: impl FnMut(&A)) {
        let _: std::ops::ControlFlow<()> = walk_terms(std::slice::from_ref(self), |t| {
            if let Term::Lit(literal) = t {
                f(literal);
            }
            std::ops::ControlFlow::Continue(true)
        });
    }

    /// Whether any application in this term has a symbol accepted by `f`.
    pub fn any_fun_sym(&self, mut f: impl FnMut(&FunSym) -> bool) -> bool {
        use std::ops::ControlFlow;
        walk_terms(std::slice::from_ref(self), |t| {
            if let Term::App(sym, _) = t
                && f(sym)
            {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(true)
            }
        })
        .is_break()
    }

    /// Whether every application in this term has a symbol accepted by `f`.
    pub fn all_fun_syms(&self, mut f: impl FnMut(&FunSym) -> bool) -> bool {
        !self.any_fun_sym(|sym| !f(sym))
    }
}

// =============================================================================
// Smart constructors
// =============================================================================

/// `lit l`: build a literal term.
pub fn lit<A>(l: A) -> Term<A> {
    Term::Lit(l)
}

/// `fApp fsym ts`: smart constructor that AC-normalises when needed.
///
/// Pre-condition: every term in `ts` must already be AC-normalised.
pub fn f_app<A: Ord + Clone>(fsym: FunSym, ts: Vec<Term<A>>) -> Term<A> {
    match fsym {
        FunSym::Ac(s) => f_app_ac(s, ts),
        FunSym::C(c) => f_app_c(c, ts),
        FunSym::List => Term::App(FunSym::List, ts.into()),
        FunSym::NoEq(_) => Term::App(fsym, ts.into()),
    }
}

/// The panic payload prefix that marks a rendered HS `error` (see
/// [`hs_error_text`]).  A control character no HS message contains, so it can
/// never collide with a payload that merely starts with the same words.
const HS_ERROR_MARKER: &str = "\u{1}tamarin-hs-error\u{1}";

/// The package id GHC stamps into the `HasCallStack` frames of this crate's
/// HS counterpart, as the pinned oracle build prints it.  Refreshed at a
/// submodule bump together with [`FAPP_AC_EMPTY_SITE`].
const TERM_ERROR_PACKAGE: &str = "tamarin-prover-term-1.13.0-HEWlVEyEBKAFHPl3i5M61g";

/// `LINE:COLUMN` of `fAppAC`'s empty-list `error` in
/// `lib/term/src/Term/Term/Raw.hs` — see [`TERM_ERROR_PACKAGE`].  The frame
/// names the path relative to the `tamarin-prover-term` package root, i.e.
/// `src/Term/Term/Raw.hs`.
const FAPP_AC_EMPTY_SITE: &str = "120:20";

/// HS `error "Term.fAppAC: empty argument list"` (Raw.hs:120).
const FAPP_AC_EMPTY_MSG: &str = "Term.fAppAC: empty argument list";

/// Raise the HS `error` at `call_site`, GHC-style.
///
/// GHC has no `Result` to return here: `error` throws, and with nothing
/// catching it the runtime prints `tamarin-prover: ` ++ `displayException`
/// (message + `HasCallStack` frame) on stderr and exits 1.  The `error`s this
/// stands in for sit below the port's error-returning layers, in code whose
/// callers cannot carry a `Result` (`Term.fAppAC`, Raw.hs:120;
/// `Main.Console.testProcess`' maude abort, Console.hs:147), so the port
/// raises a panic whose payload carries exactly the text GHC would print; the
/// binary's panic hook recognises it via [`hs_error_text`] and reproduces the
/// stream and exit code.
///
/// `call_site` is the frame's `src/<path>:<line>:<column> in <package>:<module>`
/// text, hardcoded from the oracle build at each raise site.
pub fn hs_error(message: &str, call_site: String) -> ! {
    panic!("{HS_ERROR_MARKER}{message}\nCallStack (from HasCallStack):\n  error, called at {call_site}");
}

/// The rendered HS `error` a panic payload carries, or `None` for an ordinary
/// Rust panic.  The text is `displayException`'s: the message, then the
/// one-frame `HasCallStack` block, with no trailing newline.
pub fn hs_error_text(payload: &(dyn std::any::Any + Send)) -> Option<&str> {
    payload
        .downcast_ref::<String>()?
        .strip_prefix(HS_ERROR_MARKER)
}

/// AC smart constructor: flattens nested same-symbol applications, sorts
/// the resulting argument list, and unwraps singletons.
pub fn f_app_ac<A: Ord + Clone>(sym: AcSym, args: Vec<Term<A>>) -> Term<A> {
    if args.is_empty() {
        hs_error(
            FAPP_AC_EMPTY_MSG,
            format!(
                "src/Term/Term/Raw.hs:{FAPP_AC_EMPTY_SITE} in {TERM_ERROR_PACKAGE}:Term.Term.Raw"
            ),
        );
    }
    if args.len() == 1 {
        return args.into_iter().next().unwrap();
    }
    let target = FunSym::Ac(sym);
    // Fast path: when no argument is a nested same-symbol App, the flatten
    // loop would be the identity copy, so sort `args` in place and reuse it.
    if !args
        .iter()
        .any(|a| matches!(a, Term::App(s, _) if *s == target))
    {
        let mut args = args;
        args.sort();
        return Term::App(target, args.into());
    }
    let mut flat: Vec<Term<A>> = Vec::with_capacity(args.len());
    for a in args {
        match a {
            Term::App(ref s, ref children) if *s == target => {
                flat.extend(children.iter().cloned());
            }
            _ => flat.push(a),
        }
    }
    flat.sort();
    Term::App(target, flat.into())
}

/// Commutative (non-associative) smart constructor: just sorts arguments.
pub fn f_app_c<A: Ord + Clone>(sym: CSym, mut args: Vec<Term<A>>) -> Term<A> {
    args.sort();
    Term::App(FunSym::C(sym), args.into())
}

/// Free (NoEq) smart constructor.
pub fn f_app_no_eq<A>(sym: NoEqSym, args: Vec<Term<A>>) -> Term<A> {
    Term::App(FunSym::NoEq(sym), args.into())
}

/// Smart constructor for user-defined AC terms (HS `fAppACfct`,
/// Term/Term/Raw.hs): the same AC normalisation as any other AC operator.
pub fn f_app_acfct<A: Ord + Clone>(sym: AcFctSym, args: Vec<Term<A>>) -> Term<A> {
    f_app_ac(AcSym::AcFct(sym), args)
}

/// `LIST` smart constructor.
pub fn f_app_list<A>(args: Vec<Term<A>>) -> Term<A> {
    Term::App(FunSym::List, args.into())
}

/// Direct constructor — caller must ensure AC normalisation themselves.
pub fn unsafe_f_app<A>(fsym: FunSym, args: Vec<Term<A>>) -> Term<A> {
    Term::App(fsym, args.into())
}

/// HS `fmapTerm` (Term/Term/Raw.hs:216-217), the `mapLits` of
/// Theory/Model/Formula.hs:288-291: map every literal and rebuild each
/// application through [`f_app`], so AC and C argument lists are flattened
/// and re-sorted under the order of the new literals.
pub fn map_lits<A, B: Ord + Clone>(t: &Term<A>, f: &mut dyn FnMut(&A) -> B) -> Term<B> {
    bind_lits(t, &mut |a| lit(f(a)))
}

/// Replace literals with terms, rebuilding applications through [`f_app`].
/// Visits input literals left to right and inserts each replacement once;
/// replacement terms are not visited by this traversal.
pub fn bind_lits<A, B: Ord + Clone>(t: &Term<A>, f: &mut dyn FnMut(&A) -> Term<B>) -> Term<B> {
    let mut current = t;
    let mut pending = Vec::new();
    loop {
        let mut result = match current {
            Term::Lit(a) => f(a),
            Term::App(sym, args) => {
                let mut children = args.iter();
                if let Some(first) = children.next() {
                    pending.push((*sym, children, Vec::with_capacity(args.len())));
                    current = first;
                    continue;
                }
                f_app(*sym, Vec::new())
            }
        };
        loop {
            let Some((_, children, mapped)) = pending.last_mut() else {
                return result;
            };
            mapped.push(result);
            if let Some(next) = children.next() {
                current = next;
                break;
            }
            let (sym, _, mapped) = pending.pop().unwrap();
            result = f_app(sym, mapped);
        }
    }
}

/// Replace literals once, normalizing only applications with changed children.
/// `None` preserves the original subtree; a flat application needs no worklist
/// allocation, and argument vectors are allocated only on the first change.
pub fn bind_lits_cow<A: Ord + Clone>(
    t: &Term<A>,
    f: &mut impl FnMut(&A) -> Option<Term<A>>,
) -> Option<Term<A>> {
    let args = match t {
        Term::Lit(a) => return f(a),
        Term::App(_, args) => &args[..],
    };
    struct Frame<'a, A> {
        term: &'a Term<A>,
        children: std::slice::Iter<'a, Term<A>>,
        mapped: Option<Vec<Term<A>>>,
    }

    let mut frame = Frame {
        term: t,
        children: args.iter(),
        mapped: None,
    };
    // Keep the active frame outside the Vec: a flat application needs no
    // traversal allocation. Only nested applications suspend a parent.
    let mut parents = Vec::new();
    loop {
        let changed = match frame.children.next() {
            Some(term @ Term::App(_, args)) if !args.is_empty() => {
                parents.push(frame);
                frame = Frame {
                    term,
                    children: args.iter(),
                    mapped: None,
                };
                continue;
            }
            Some(Term::Lit(a)) => f(a),
            Some(Term::App(..)) => None,
            None => {
                let result = frame.mapped.map(|mapped| match frame.term {
                    Term::App(sym, _) => f_app(*sym, mapped),
                    Term::Lit(_) => unreachable!(),
                });
                let Some(parent) = parents.pop() else {
                    return result;
                };
                frame = parent;
                result
            }
        };
        // Match cow_map_vec: clone the untouched prefix only at the first
        // reported change. The iterator has consumed the completed child, so
        // subtract its remaining length and that child to locate the prefix.
        // Images are inserted once, never substituted again.
        if let Some(changed) = changed {
            frame
                .mapped
                .get_or_insert_with(|| {
                    let Term::App(_, args) = frame.term else {
                        unreachable!()
                    };
                    let mut mapped = Vec::with_capacity(args.len());
                    mapped.extend_from_slice(&args[..args.len() - frame.children.len() - 1]);
                    mapped
                })
                .push(changed);
        } else if let Some(mapped) = &mut frame.mapped {
            let Term::App(_, args) = frame.term else {
                unreachable!()
            };
            mapped.push(args[args.len() - frame.children.len() - 1].clone());
        }
    }
}

/// Maximum number of term nodes on any root-to-leaf path.
pub fn term_depth<A>(t: &Term<A>) -> usize {
    let mut current = (std::slice::from_ref(t).iter(), 1usize);
    let mut pending = Vec::new();
    let mut maximum = 1;
    loop {
        while let Some(node) = current.0.next() {
            maximum = maximum.max(current.1);
            if let Term::App(_, args) = node
                && !args.is_empty()
            {
                let depth = current.1.saturating_add(1);
                if !current.0.as_slice().is_empty() {
                    pending.push(current);
                }
                current = (args.iter(), depth);
            }
        }
        let Some(next) = pending.pop() else {
            return maximum;
        };
        current = next;
    }
}

// =============================================================================
// Subterm tests / counts
// =============================================================================

pub fn is_subterm<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> bool {
    use std::ops::ControlFlow;
    walk_terms(std::slice::from_ref(haystack), |node| {
        if needle == node {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(true)
        }
    })
    .is_break()
}

pub fn is_proper_subterm<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> bool {
    match haystack {
        Term::App(_, ts) => ts.iter().any(|t| is_subterm(needle, t)),
        Term::Lit(_) => false,
    }
}

pub fn count_subterms<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> usize {
    let mut count = 0;
    let _: std::ops::ControlFlow<()> = walk_terms(std::slice::from_ref(haystack), |node| {
        let matched = needle == node;
        count += usize::from(matched);
        std::ops::ControlFlow::Continue(!matched)
    });
    count
}

pub fn count_proper_subterms<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> usize {
    match haystack {
        Term::App(_, ts) => ts.iter().map(|t| count_subterms(needle, t)).sum(),
        Term::Lit(_) => 0,
    }
}

// =============================================================================
// "Protected" subterms (auto-sources).
// NB (HS Term/Term.hs:254-255): anything but a pair or an AC symbol is "protected".
// =============================================================================

/// `True` iff the term's top symbol is an AC operator. Port of HS `isAC`
/// (Term/Term.hs:229-231).
pub fn is_ac<A>(t: &Term<A>) -> bool {
    matches!(t, Term::App(FunSym::Ac(_), _))
}

/// `True` iff the term is a pair `<_,_>`. Port of HS `isPair`
/// (Term/Term.hs:185-187, `viewTerm2 -> FPair _ _`): top symbol is the binary
/// `pair` constructor.
pub fn is_pair<A>(t: &Term<A>) -> bool {
    match t {
        Term::App(FunSym::NoEq(s), args) => {
            *s == crate::function_symbols::pair_sym() && args.len() == 2
        }
        _ => false,
    }
}

/// `True` iff the term is a DH product `_*_`. Port of HS `isProduct`
/// (Term/Term.hs:200-202, `viewTerm2 -> FMult _`): top symbol is the AC
/// multiplication operator.
pub fn is_product<A>(t: &Term<A>) -> bool {
    matches!(t, Term::App(FunSym::Ac(AcSym::Mult), _))
}

/// `True` iff the term is a well-formed inverse `inv(_)`. Port of HS `isInverse`
/// (Term/Term.hs:195-197, `viewTerm2 -> FInv _`): the unary `inv` operator
/// applied to one argument.
pub fn is_inverse<A>(t: &Term<A>) -> bool {
    match t {
        Term::App(FunSym::NoEq(s), args) => {
            s.name == crate::function_symbols::INV_SYM_STRING && args.len() == 1
        }
        _ => false,
    }
}

/// All "protected" subterms of `t`: subterms whose top symbol is a function
/// that is neither a pair nor an AC operator. Port of HS `allProtSubterms`
/// (Term/Term.hs:260-265) — pre-order, descending through pairs/AC operators.
pub fn all_prot_subterms<A: Clone>(t: &Term<A>) -> Vec<Term<A>> {
    let mut out = Vec::new();
    let _: std::ops::ControlFlow<()> = walk_terms(std::slice::from_ref(t), |node| {
        if matches!(node, Term::App(..)) && !is_pair(node) && !is_ac(node) {
            out.push(node.clone());
        }
        std::ops::ControlFlow::Continue(true)
    });
    out
}

// =============================================================================
// Replacement helpers (top-down)
// =============================================================================

pub fn replace_subterm<A: Clone, F: FnMut(Term<A>) -> Term<A>>(f: &mut F, t: Term<A>) -> Term<A> {
    rewrite_subterms(f, t, true)
}

pub fn replace_proper_subterm<A: Clone, F: FnMut(Term<A>) -> Term<A>>(
    f: &mut F,
    t: Term<A>,
) -> Term<A> {
    rewrite_subterms(f, t, false)
}

fn rewrite_subterms<A: Clone>(
    f: &mut impl FnMut(Term<A>) -> Term<A>,
    mut current: Term<A>,
    mut visit: bool,
) -> Term<A> {
    let mut pending = Vec::new();
    loop {
        if visit {
            current = f(current);
        }
        visit = true;
        if let Term::App(sym, args) = current {
            if let Some(first) = args.first() {
                current = first.clone();
                let output = Vec::with_capacity(args.len());
                pending.push((sym, args, 1, output));
                continue;
            }
            current = Term::App(sym, Vec::new().into());
        }
        loop {
            let Some((_, args, index, output)) = pending.last_mut() else {
                return current;
            };
            output.push(current);
            if let Some(next) = args.get(*index) {
                current = next.clone();
                *index += 1;
                break;
            }
            let (sym, _, _, output) = pending.pop().unwrap();
            // Replacement preserves the original raw constructor behavior;
            // unlike map_lits, this must not re-normalize AC arguments.
            current = Term::App(sym, output.into());
        }
    }
}

// =============================================================================
// TermSize: structural size including AC arg count.
// =============================================================================

/// Port of Haskell's `Sized` type class (`Term/Term/Classes.hs`).
/// Renamed from `Sized` to avoid clashing with the built-in
/// `std::marker::Sized` marker trait.
pub trait TermSize {
    fn size(&self) -> usize;
}

// Port of `instance Sized a => Sized (Term a)` (Term/Term/Raw.hs:247-248).
impl<A: TermSize> TermSize for Term<A> {
    fn size(&self) -> usize {
        let mut total = 0;
        let _: std::ops::ControlFlow<()> = walk_terms(std::slice::from_ref(self), |node| {
            total += match node {
                Term::Lit(a) => a.size(),
                Term::App(..) => 1,
            };
            std::ops::ControlFlow::Continue(true)
        });
        total
    }
}

// Port of `instance Sized (Lit c v) where size _ = 1` (VTerm.hs:95-96).
// This is what makes `TermSize` reachable for real `VTerm`/`LNTerm`.
impl<C, V> TermSize for crate::vterm::Lit<C, V> {
    fn size(&self) -> usize {
        1
    }
}

// Sensible default impls for the literal types we'll actually use.
impl TermSize for u64 {
    fn size(&self) -> usize {
        1
    }
}
impl TermSize for i64 {
    fn size(&self) -> usize {
        1
    }
}
impl TermSize for String {
    fn size(&self) -> usize {
        1
    }
}
impl TermSize for &str {
    fn size(&self) -> usize {
        1
    }
}

// =============================================================================
// `show`: Haskell's raw `Show (Term a)`
// =============================================================================

/// A term literal that renders through Haskell's `show`.
///
/// The `Show a` constraint of HS `instance Show a => Show (Term a)`
/// (Term/Term/Raw.hs:227-237).
pub trait ShowLit {
    /// Append `show self` to `out`.
    fn show_into(&self, out: &mut String);
}

/// HS `instance Show a => Show (Term a)` (Term/Term/Raw.hs:227-237).
///
/// Every application is prefix and its arguments are separated by a bare comma;
/// a `NoEq` or user-`AC` symbol applied to no arguments writes its name alone.
/// This is a different rendering from [`crate::pretty::pretty_lnterm`]: `pair`
/// and `exp` applications keep their prefix form instead of turning into
/// `<a, b>` and `a^b`, and each of the four builtin AC operators writes the
/// `ACSym` constructor name its derived `Show` gives
/// (Term/Term/FunctionSymbols.hs:138-139) instead of an infix operator.
pub fn show_term<A: ShowLit>(t: &Term<A>) -> String {
    let mut out = String::new();
    write_show_term(t, &mut out);
    out
}

fn write_show_term<A: ShowLit>(t: &Term<A>, out: &mut String) {
    match t {
        Term::Lit(l) => l.show_into(out),
        Term::App(sym, args) => {
            // `FApp (NoEq (s,_)) []` and `FApp (AC (ACfct (s,_))) []` are the
            // two arms that stop at the symbol name; `C EMap`, `List` and the
            // builtin AC operators write a parenthesised argument list whether
            // or not it is empty.
            let (name, bare_when_nullary): (Cow<'_, str>, bool) = match sym {
                FunSym::NoEq(s) => (String::from_utf8_lossy(s.name), true),
                FunSym::Ac(AcSym::AcFct(s)) => (String::from_utf8_lossy(s.name), true),
                FunSym::C(CSym::EMap) => (String::from_utf8_lossy(EMAP_SYM_STRING), false),
                FunSym::List => (Cow::Borrowed("LIST"), false),
                FunSym::Ac(AcSym::Union) => (Cow::Borrowed("Union"), false),
                FunSym::Ac(AcSym::Mult) => (Cow::Borrowed("Mult"), false),
                FunSym::Ac(AcSym::Xor) => (Cow::Borrowed("Xor"), false),
                FunSym::Ac(AcSym::NatPlus) => (Cow::Borrowed("NatPlus"), false),
            };
            out.push_str(&name);
            if !(args.is_empty() && bare_when_nullary) {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_show_term(a, out);
                }
                out.push(')');
            }
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{exp_sym, pair_sym, AcSym, CSym, FunSym};

    /// The pinned submodule's `lib/term/src/Term/Term/Raw.hs`, embedded at
    /// build time.
    const RAW_HS: &str = include_str!("../../../tamarin-prover/lib/term/src/Term/Term/Raw.hs");

    #[test]
    fn literal_binding_visits_inputs_once_and_cleans_up_on_panic() {
        let input = f_app_list(vec![lit(0u8), lit(1)]);
        let mut seen = Vec::new();
        let result = bind_lits(&input, &mut |v| {
            seen.push(*v);
            f_app_list(vec![lit(v + 2)])
        });
        assert_eq!(seen, [0, 1]);
        assert_eq!(
            result,
            f_app_list(vec![f_app_list(vec![lit(2)]), f_app_list(vec![lit(3)])])
        );

        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut deep = lit(0u8);
                for _ in 0..100_000 {
                    deep = f_app_list(vec![deep]);
                }
                let tree = f_app_list(vec![deep, lit(9)]);
                // The deep left result is complete when the right callback fails.
                assert!(std::panic::catch_unwind(|| {
                    bind_lits(&tree, &mut |v| {
                        assert_ne!(*v, 9, "fail after completing the left child");
                        lit(7u8)
                    })
                })
                .is_err());
                drop(tree);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn last_owner_drop_is_iterative_and_preserves_leaf_order() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                struct Leaf(usize, Arc<std::sync::Mutex<Vec<usize>>>);
                impl Drop for Leaf {
                    fn drop(&mut self) {
                        self.1.lock().unwrap().push(self.0);
                    }
                }
                let dropped = Arc::new(std::sync::Mutex::new(Vec::new()));
                let mut term = Term::Lit(Leaf(0, dropped.clone()));
                for i in 1..100_000 {
                    term = Term::App(
                        FunSym::NoEq(pair_sym()),
                        vec![term, Term::Lit(Leaf(i, dropped.clone()))].into(),
                    );
                }
                drop(term);
                assert_eq!(*dropped.lock().unwrap(), (0..100_000).collect::<Vec<_>>());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn shared_terms_release_leaves_once_even_across_threads() {
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Barrier,
        };
        #[derive(Clone)]
        struct Leaf(Arc<AtomicUsize>);
        impl Drop for Leaf {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }
        for _ in 0..8 {
            let dropped = Arc::new(AtomicUsize::new(0));
            let mut term = Term::App(
                FunSym::NoEq(pair_sym()),
                vec![Term::Lit(Leaf(dropped.clone()))].into(),
            );
            for _ in 0..100_000 {
                term = Term::App(FunSym::NoEq(pair_sym()), vec![term.clone(), term].into());
            }
            drop(term.clone());
            assert_eq!(dropped.load(Ordering::Relaxed), 0);
            let barrier = Arc::new(Barrier::new(2));
            let threads: Vec<_> = [term.clone(), term]
                .map(|term| Term::App(FunSym::NoEq(pair_sym()), vec![term].into()))
                .into_iter()
                .map(|term| {
                    let barrier = barrier.clone();
                    std::thread::Builder::new()
                        .stack_size(256 * 1024)
                        .spawn(move || {
                            barrier.wait();
                            drop(term);
                        })
                        .unwrap()
                })
                .collect();
            for thread in threads {
                thread.join().unwrap();
            }
            assert_eq!(dropped.load(Ordering::Relaxed), 1);
        }
    }

    /// [`FAPP_AC_EMPTY_SITE`] is pasted verbatim into a `HasCallStack` frame
    /// the port must emit byte-for-byte, and the stderr tests for that frame
    /// compare the port against bytes captured from the port — so they agree
    /// with a stale coordinate.  Read it back out of the pinned source.
    #[test]
    fn fapp_ac_empty_site_is_the_pinned_call_site() {
        let (idx, line) = RAW_HS
            .lines()
            .enumerate()
            .find(|(_, l)| l.contains(FAPP_AC_EMPTY_MSG))
            .expect("no `fAppAC` empty-list `error` in the pinned Raw.hs");
        let col = line.find("error").expect("no `error` token") + 1;
        assert_eq!(FAPP_AC_EMPTY_SITE, format!("{}:{}", idx + 1, col));
    }

    fn nat(n: u64) -> Term<u64> {
        lit(n)
    }

    #[test]
    fn ac_flattens_and_sorts() {
        // mult(mult(3, 1), 2) → mult(1, 2, 3)
        let inner = f_app_ac(AcSym::Mult, vec![nat(3), nat(1)]);
        let outer = f_app_ac(AcSym::Mult, vec![inner, nat(2)]);
        match outer {
            Term::App(FunSym::Ac(AcSym::Mult), ref ts) => {
                let lits: Vec<u64> = ts
                    .iter()
                    .map(|t| match t {
                        Term::Lit(n) => *n,
                        _ => unreachable!(),
                    })
                    .collect();
                assert_eq!(lits, vec![1, 2, 3]);
            }
            _ => panic!("expected AC Mult application"),
        }
    }

    #[test]
    fn ac_singleton_unwrap() {
        let t = f_app_ac(AcSym::Mult, vec![nat(7)]);
        assert_eq!(t, nat(7));
    }

    #[test]
    fn prot_subterms_descend_through_pair_and_ac() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        let h1 = NoEqSym::new(b"h", 1, Privacy::Public, Constructability::Constructor);
        let mk_h = |x: Term<u64>| Term::App(FunSym::NoEq(h1), vec![x].into());
        // pair(h(1), mult(h(2), 3)): protected subterms are h(1), h(2)
        // (descend through pair and the AC mult; bare 3 is a Lit → none).
        let pr = Term::App(
            FunSym::NoEq(pair_sym()),
            vec![
                mk_h(nat(1)),
                f_app_ac(AcSym::Mult, vec![mk_h(nat(2)), nat(3)]),
            ]
            .into(),
        );
        assert!(is_pair(&pr));
        assert!(!is_ac(&pr));
        let subs = all_prot_subterms(&pr);
        assert_eq!(subs, vec![mk_h(nat(1)), mk_h(nat(2))]);
        // A protected term itself: its top is returned, then its protected children.
        assert_eq!(all_prot_subterms(&mk_h(nat(1))), vec![mk_h(nat(1))]);
        // A bare literal has no protected subterms.
        assert_eq!(all_prot_subterms(&nat(5)), Vec::<Term<u64>>::new());
    }

    /// An Xor that is already flat, inside another Xor, gives exactly one Xor
    /// over the union of the arguments.  The constructor sorts that union
    /// again.  It merges the new argument into the flattened list.  It does
    /// not add the new argument after that list.
    #[test]
    fn ac_flattening_absorbs_a_nested_same_symbol_app() {
        let t1 = f_app_ac(AcSym::Xor, vec![nat(1), nat(2), nat(3)]);
        let t2 = f_app_ac(AcSym::Xor, vec![t1, nat(0)]);
        assert_eq!(
            t2,
            unsafe_f_app(FunSym::Ac(AcSym::Xor), vec![nat(0), nat(1), nat(2), nat(3)])
        );
    }

    #[test]
    fn c_sorts_arguments() {
        let t = f_app_c(CSym::EMap, vec![nat(2), nat(1)]);
        match t {
            Term::App(FunSym::C(CSym::EMap), ts) => {
                assert_eq!(&*ts, &[nat(1), nat(2)]);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn no_eq_preserves_order() {
        // pair(1, 2) keeps argument order; pair is not commutative.
        let t = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
        match t {
            Term::App(FunSym::NoEq(s), ts) => {
                assert_eq!(s, pair_sym());
                assert_eq!(&*ts, &[nat(1), nat(2)]);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn subterm_basics() {
        let inner = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
        let outer = f_app_no_eq(exp_sym(), vec![inner.clone(), nat(3)]);
        assert!(is_subterm(&inner, &outer));
        assert!(is_subterm(&nat(2), &outer));
        assert!(!is_subterm(&nat(99), &outer));
        // A term is its own subterm but not its own proper subterm.
        assert!(is_subterm(&outer, &outer));
        assert!(!is_proper_subterm(&outer, &outer));
    }

    #[test]
    fn count_subterms_counts_occurrences() {
        // pair(x, pair(x, y)) contains x twice.
        let x = nat(1);
        let y = nat(2);
        let inner = f_app_no_eq(pair_sym(), vec![x.clone(), y.clone()]);
        let outer = f_app_no_eq(pair_sym(), vec![x.clone(), inner]);
        assert_eq!(count_subterms(&x, &outer), 2);
        assert_eq!(count_subterms(&y, &outer), 1);
    }

    /// [`replace_subterm`] applies `f` to the complete term first.  It then
    /// descends into the result of `f`.  So it also visits the new subterms
    /// that a rewrite introduces.  It never visits the original children of a
    /// node that `f` replaced.
    ///
    /// A bottom-up traversal visits the children first and applies `f` last.
    /// That order gives the same result for an `f` that changes only leaves.
    /// So the `f` here maps an `exp` node onto a `pair` of two new leaves.
    /// The top-down order rewrites the top node.  It then increments the two
    /// leaves it has just introduced.  It never sees the original `1` and
    /// `2`.  [`replace_proper_subterm`] runs the same descent, but it does
    /// not apply `f` at the root.
    #[test]
    fn replace_subterm_is_top_down() {
        let t = f_app_no_eq(exp_sym(), vec![nat(1), nat(2)]);
        let mut f = |t: Term<u64>| match t {
            Term::Lit(n) => Term::Lit(n + 10),
            Term::App(s, _) if s == FunSym::NoEq(exp_sym()) => {
                f_app_no_eq(pair_sym(), vec![nat(7), nat(8)])
            }
            other => other,
        };
        assert_eq!(
            replace_subterm(&mut f, t.clone()),
            f_app_no_eq(pair_sym(), vec![nat(17), nat(18)])
        );
        // `replace_proper_subterm` skips the root.  The `exp` node stays.
        // Each child goes to the full top-down `replace_subterm`.
        assert_eq!(
            replace_proper_subterm(&mut f, t),
            f_app_no_eq(exp_sym(), vec![nat(11), nat(12)])
        );
    }

    /// The hand-written `PartialEq`/`Ord`/`PartialOrd`/`Hash` on [`Term`]
    /// contain an `Arc::ptr_eq` fast path.  So they must still give exactly
    /// the answers of the derived, purely structural implementations.  That
    /// means three things.  `Lit` comes before `App`, which is the
    /// declaration order.  That order puts constants before applications in
    /// every `f_app_ac`/`f_app_c` argument sort.  Inside `App`, the symbol
    /// comes before the arguments.  The answer is the same whether or not the
    /// two argument slices are the same allocation.
    #[test]
    fn term_ord_is_structural_whether_or_not_args_are_shared() {
        use std::cmp::Ordering;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        fn hash_of(t: &Term<u64>) -> u64 {
            let mut h = DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        }
        // `Lit` sorts before `App`, for any payloads.
        let big_lit = nat(u64::MAX);
        let app = f_app_no_eq(pair_sym(), vec![nat(0), nat(0)]);
        assert!(big_lit < app);
        assert_eq!(app.cmp(&big_lit), Ordering::Greater);
        assert_eq!(big_lit.partial_cmp(&app), Some(Ordering::Less));
        assert!(big_lit != app);
        // Inside `App`, the symbol has priority over the arguments.  `exp` is
        // less than `pair` in `NoEqSym` order.  So `exp(9,9)` sorts below
        // `pair(0,0)`.
        assert!(exp_sym() < pair_sym());
        let exp_big = f_app_no_eq(exp_sym(), vec![nat(9), nat(9)]);
        let pair_small = f_app_no_eq(pair_sym(), vec![nat(0), nat(0)]);
        assert!(exp_big < pair_small);
        // Here are two argument slices: one shared, one built separately.
        // `shared` is a clone, so it holds the same `Arc` and the pointer
        // fast path applies.  `rebuilt` is an equal slice at a different
        // address, so the fast path does not apply and the structural walk
        // gives the answer.  All three answers must be the same.
        let shared = app.clone();
        let rebuilt = f_app_no_eq(pair_sym(), vec![nat(0), nat(0)]);
        if let (Term::App(_, a), Term::App(_, b), Term::App(_, c)) = (&app, &shared, &rebuilt) {
            assert!(a.ptr_eq(b));
            assert!(!a.ptr_eq(c));
        } else {
            panic!("expected three applications");
        }
        for other in [&shared, &rebuilt] {
            assert_eq!(&app, other);
            assert_eq!(app.cmp(other), Ordering::Equal);
            assert_eq!(app.partial_cmp(other), Some(Ordering::Equal));
            // `Hash` must agree with that `Eq`.  `Hash` uses the content, so
            // the term with the shared pointer and the rebuilt term give the
            // same hash.
            assert_eq!(hash_of(&app), hash_of(other));
        }
        // The comparison still finds a different argument through the
        // fast-path guard.
        let differing = f_app_no_eq(pair_sym(), vec![nat(0), nat(1)]);
        assert_ne!(app, differing);
        assert_eq!(app.cmp(&differing), Ordering::Less);
    }

    // =========================================================================
    // Haskell-faithfulness invariants for AC/C/NoEq term constructors.
    // =========================================================================

    /// AC terms with the same multiset are *equal* mod-AC: `+(a, b)` and
    /// `+(b, a)` get sorted to the same canonical form, so structural
    /// equality holds.  Haskell-faithful: AC canonicalization happens at
    /// construction time (`fAppAC` in Term/Term/Raw.hs).
    #[test]
    fn ac_terms_are_equal_modulo_argument_order() {
        let t1 = f_app_ac(AcSym::Mult, vec![nat(7), nat(2), nat(5)]);
        let t2 = f_app_ac(AcSym::Mult, vec![nat(5), nat(7), nat(2)]);
        let t3 = f_app_ac(AcSym::Mult, vec![nat(2), nat(5), nat(7)]);
        assert_eq!(
            t1, t2,
            "AC terms with same multiset of args must compare equal — \
             smart constructor canonicalizes order"
        );
        assert_eq!(t1, t3);
    }

    /// AC vs C distinction: C terms ARE sorted but NOT flattened.  NoEq
    /// terms preserve argument order.
    #[test]
    fn ac_flattens_but_c_does_not() {
        // AC: mult(mult(1,2), 3) → mult(1,2,3) — flat.
        let nested_ac = f_app_ac(
            AcSym::Mult,
            vec![f_app_ac(AcSym::Mult, vec![nat(1), nat(2)]), nat(3)],
        );
        match &nested_ac {
            Term::App(FunSym::Ac(AcSym::Mult), ts) => {
                assert_eq!(ts.len(), 3, "AC must flatten nested same-sym");
            }
            _ => panic!(),
        }
        // C is non-associative; nested EMap doesn't flatten.
        let nested_c = f_app_c(
            CSym::EMap,
            vec![f_app_c(CSym::EMap, vec![nat(1), nat(2)]), nat(3)],
        );
        match &nested_c {
            Term::App(FunSym::C(CSym::EMap), ts) => {
                assert_eq!(ts.len(), 2, "C must NOT flatten — non-associative");
            }
            _ => panic!(),
        }
    }

    /// Lit::Con < Lit::Var: constants sort before variables.
    /// VTerm.hs:56: `data Lit c v = Con c | Var v`.
    ///
    /// This matters for `f_app_ac`/`f_app_c` argument sorting: if a
    /// term mixes constants and variables, constants always sort first.
    /// Downstream code in atom_valuation expects constants in fixed
    /// positions when matching.
    #[test]
    fn lit_con_sorts_before_lit_var() {
        use crate::lterm::{LNTerm, LSort, LVar, Name, NameId, NameTag};
        use crate::vterm::Lit;

        // Variant tags: Con=0, Var=1 in Haskell decl order.
        let pub_a = Name {
            tag: NameTag::Pub,
            id: NameId::new("a"),
        };
        let v_x = LVar::new("x", LSort::Msg, 0);
        let con: LNTerm = Term::Lit(Lit::Con(pub_a));
        let var: LNTerm = Term::Lit(Lit::Var(v_x));
        assert!(
            con < var,
            "Lit::Con must sort before Lit::Var (Haskell decl order). \
                 AC term canonicalization relies on this — `+(x, 'a')` \
                 canonicalizes to `+('a', x)`."
        );
    }

    /// `BVar::Bound < BVar::Free` from LTerm.hs:451-453 declaration order.
    /// `data BVar v = Bound Integer | Free v`
    ///
    /// This drives the BTreeMap key order for guarded-formula
    /// binders/bound-var lookup — when we de Bruijn-index a formula's
    /// quantified variables, the bound positions sort before any free
    /// occurrences.
    #[test]
    fn bvar_bound_sorts_before_bvar_free() {
        use crate::lterm::{BVar, LSort, LVar};
        let bound: BVar<LVar> = BVar::Bound(5);
        let free: BVar<LVar> = BVar::Free(LVar::new("x", LSort::Msg, 0));
        assert!(
            bound < free,
            "BVar::Bound must sort before BVar::Free \
                 (Haskell LTerm.hs:451 declaration order)"
        );
    }

    /// `fAppAC _ [] = error "Term.fAppAC: empty argument list"` (Raw.hs:120).
    /// The payload carries GHC's `displayException` text so the binary's hook
    /// can print it verbatim; the end-to-end stderr and exit code are pinned in
    /// `tamarin-prover/tests/ac_empty_args_error.rs`.
    #[test]
    fn empty_ac_argument_list_raises_the_hs_error_payload() {
        use crate::function_symbols::AcSym;

        let raised = std::panic::catch_unwind(|| f_app_ac::<u32>(AcSym::Mult, Vec::new()))
            .expect_err("an empty argument list must raise");
        assert_eq!(
            hs_error_text(raised.as_ref()),
            Some(
                "Term.fAppAC: empty argument list\nCallStack (from HasCallStack):\n  \
                 error, called at src/Term/Term/Raw.hs:120:20 in \
                 tamarin-prover-term-1.13.0-HEWlVEyEBKAFHPl3i5M61g:Term.Term.Raw"
            )
        );
        // An ordinary Rust panic keeps Rust's own report.
        let plain =
            std::panic::catch_unwind(|| panic!("boom")).expect_err("the closure must panic");
        assert_eq!(hs_error_text(plain.as_ref()), None);
    }

    /// `map_lits` rebuilds every application with `f_app`, so swapping the
    /// literals of an AC term re-sorts its operands instead of keeping the
    /// mapped literals in their original positions.
    #[test]
    fn map_lits_rebuilds_ac_through_f_app() {
        use crate::lterm::{LNTerm, LSort, LVar};
        use crate::vterm::{var_term, Lit};

        let x = LVar::new("x", LSort::Msg, 0);
        let z = LVar::new("z", LSort::Msg, 0);
        let prod: LNTerm = f_app(FunSym::Ac(AcSym::Mult), vec![var_term(x), var_term(z)]);
        let Term::App(_, args) = &prod else {
            panic!("expected an AC application");
        };
        assert_eq!(&args[..], &[var_term(x), var_term(z)]);

        let swapped = map_lits(&prod, &mut |l| match l {
            Lit::Var(v) if *v == x => Lit::Var(z),
            Lit::Var(v) if *v == z => Lit::Var(x),
            other => *other,
        });
        let Term::App(_, args) = &swapped else {
            panic!("expected an AC application");
        };
        assert_eq!(&args[..], &[var_term(x), var_term(z)]);
        assert_eq!(swapped, prod);
    }

    // =========================================================================
    // `show_term` — the raw Haskell `Show (Term a)` form.
    // =========================================================================

    /// The literal type the `show_term` tests build over.
    type ShowT = crate::vterm::VTerm<crate::lterm::Name, crate::lterm::LVar>;

    fn show_msg_var(name: &str) -> ShowT {
        use crate::lterm::{LSort, LVar};
        crate::vterm::var_term(LVar::new(name, LSort::Msg, 0))
    }

    fn show_noeq(name: &[u8], arity: usize) -> NoEqSym {
        use crate::function_symbols::{Constructability, Privacy};
        NoEqSym::new(
            name.to_vec(),
            arity,
            Privacy::Public,
            Constructability::Constructor,
        )
    }

    fn show_acfct(name: &[u8]) -> AcFctSym {
        use crate::function_symbols::{Constructability, NdcState, Privacy};
        AcFctSym::new(
            name.to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        )
    }

    /// `FApp (NoEq (s,_)) [] -> BC.unpack s` and
    /// `FApp (AC (ACfct (s,_))) [] -> BC.unpack s` (Term/Raw.hs:227-237, see
    /// line 231): the two nullary arms write the name alone.
    #[test]
    fn show_term_writes_a_nullary_symbol_without_parentheses() {
        let g: ShowT = f_app_no_eq(show_noeq(b"g", 0), vec![]);
        assert_eq!(show_term(&g), "g");
        let nil: ShowT = unsafe_f_app(FunSym::Ac(AcSym::AcFct(show_acfct(b"nil"))), vec![]);
        assert_eq!(show_term(&nil), "nil");
    }

    /// `intercalate ","` (Term/Raw.hs:227-237, see line 232): no space follows
    /// a comma, and each argument is itself shown, so the form nests.
    #[test]
    fn show_term_writes_comma_separated_arguments() {
        let (x, y) = (show_msg_var("x"), show_msg_var("y"));
        let inner = f_app_no_eq(show_noeq(b"h", 2), vec![x.clone(), y.clone()]);
        assert_eq!(show_term(&inner), "h(x,y)");
        let outer = f_app_no_eq(show_noeq(b"k", 3), vec![inner, x, f_app_list(vec![y])]);
        assert_eq!(show_term(&outer), "k(h(x,y),x,LIST(y))");
    }

    /// `FApp (AC o) as -> show o ++ …` (Term/Raw.hs:227-237, see line 237)
    /// writes the derived `ACSym` constructor name
    /// (Term/Term/FunctionSymbols.hs:138-139); the `ACfct` arm (see line 234)
    /// writes the user symbol's own name instead.
    #[test]
    fn show_writes_an_ac_head_by_its_constructor_name() {
        let (x, y) = (show_msg_var("x"), show_msg_var("y"));
        for (sym, name) in [
            (AcSym::Union, "Union"),
            (AcSym::Mult, "Mult"),
            (AcSym::Xor, "Xor"),
            (AcSym::NatPlus, "NatPlus"),
        ] {
            let t: ShowT = f_app_ac(sym, vec![x.clone(), y.clone()]);
            assert_eq!(show_term(&t), format!("{}(x,y)", name));
        }
        let user: ShowT = f_app_acfct(show_acfct(b"xorr"), vec![x, y]);
        assert_eq!(show_term(&user), "xorr(x,y)");
    }

    /// `pair` and `exp` are `NoEq` symbols, so `show` writes them prefix; the
    /// `<a, b>` and `a^b` spellings belong to `prettyTerm`.
    #[test]
    fn show_writes_a_pairing_as_the_prefix_symbol() {
        use crate::lterm::pub_term;
        let p: ShowT = f_app_no_eq(pair_sym(), vec![pub_term("a"), pub_term("b")]);
        assert_eq!(show_term(&p), "pair('a','b')");
        let e: ShowT = f_app_no_eq(exp_sym(), vec![p, pub_term("c")]);
        assert_eq!(show_term(&e), "exp(pair('a','b'),'c')");
    }
}

#[cfg(test)]
mod iterative_operations_tests {
    use super::*;
    use std::hash::{Hash, Hasher};

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Reference {
        Lit(u64),
        App(FunSym, Vec<Reference>),
    }
    fn reference(t: &Term<u64>) -> Reference {
        match t {
            Term::Lit(a) => Reference::Lit(*a),
            Term::App(s, args) => Reference::App(*s, args.iter().map(reference).collect()),
        }
    }
    // Record the byte stream, not just a potentially colliding final hash.
    #[derive(Default)]
    struct Bytes(Vec<u8>);
    impl Hasher for Bytes {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes);
        }
    }
    fn old_hash(t: &Term<u64>, h: &mut Bytes) {
        match t {
            Term::Lit(a) => {
                0u8.hash(h);
                a.hash(h);
            }
            Term::App(s, args) => {
                1u8.hash(h);
                s.hash(h);
                args.len().hash(h);
                for child in args.iter() {
                    old_hash(child, h);
                }
            }
        }
    }

    #[test]
    fn structural_operations_preserve_order_hash_stream_and_debug_flags() {
        let mut terms = vec![lit(0u64), lit(15), f_app_list(vec![])];
        for i in 0..80 {
            let children = (0..i % 4)
                .map(|j| terms[(i * 7 + j * 3) % terms.len()].clone())
                .collect();
            let symbol = if i % 2 == 0 {
                FunSym::List
            } else {
                FunSym::Ac(AcSym::Xor)
            };
            terms.push(unsafe_f_app(symbol, children));
        }
        for a in &terms {
            let expected = reference(a);
            for b in &terms {
                let rhs = reference(b);
                assert_eq!(a == b, expected == rhs);
                assert_eq!(a.cmp(b), expected.cmp(&rhs));
                assert_eq!(a.partial_cmp(b), expected.partial_cmp(&rhs));
            }
            let mut old = Bytes::default();
            let mut new = Bytes::default();
            old_hash(a, &mut old);
            a.hash(&mut new);
            assert_eq!(old.0, new.0);
            assert_eq!(format!("{a:?}"), format!("{expected:?}"));
            assert_eq!(format!("{a:#?}"), format!("{expected:#?}"));
            assert_eq!(format!("{a:08x?}"), format!("{expected:08x?}"));
            assert_eq!(format!("{a:+20.3?}"), format!("{expected:+20.3?}"));
        }
        // Partial order must not turn an incomparable leaf into equality,
        // nor inspect it when an earlier field already decides the result.
        let a = f_app_list(vec![lit(f64::NAN)]);
        let b = f_app_list(vec![lit(f64::NAN)]);
        assert_eq!(a.partial_cmp(&b), None);
        assert_eq!(a.partial_cmp(&a.clone()), Some(std::cmp::Ordering::Equal));
        let a = f_app_list(vec![lit(0.0), a]);
        let b = f_app_list(vec![lit(1.0), b]);
        assert_eq!(a.partial_cmp(&b), Some(std::cmp::Ordering::Less));
    }

    #[test]
    fn deep_structural_operations_use_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let build = |leaf| {
                    let mut term = lit(leaf);
                    for _ in 0..100_000 {
                        term = f_app_list(vec![term]);
                    }
                    term
                };
                let a = build(0u64);
                let b = build(0);
                let c = build(1);
                assert!(a == b && a != c);
                assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal);
                assert_eq!(a.cmp(&c), std::cmp::Ordering::Less);
                assert_eq!(a.partial_cmp(&c), Some(std::cmp::Ordering::Less));
                let mut state = std::collections::hash_map::DefaultHasher::new();
                a.hash(&mut state);
                let printed = format!("{a:?}");
                assert!(printed.starts_with("App(List, [App(List, ["));
                assert!(printed.contains("Lit(0)"));
                // Drop all last owners on the same small stack.
                drop((a, b, c));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn debug_propagates_writer_errors() {
        struct Fail;
        impl std::fmt::Write for Fail {
            fn write_str(&mut self, _: &str) -> std::fmt::Result {
                Err(std::fmt::Error)
            }
        }
        use std::fmt::Write;
        assert!(write!(Fail, "{:?}", f_app_list(vec![lit(1)])).is_err());
    }
}

#[cfg(test)]
mod walker_tests {
    use super::*;

    #[test]
    fn walkers_keep_callback_order_pruning_and_raw_replacement() {
        let t = f_app_list(vec![f_app_list(vec![lit(1u64), lit(2)]), lit(3)]);
        let mut seen = Vec::new();
        let mapped = map_lits(&t, &mut |n| {
            seen.push(*n);
            4 - n
        });
        assert_eq!(seen, [1, 2, 3]);
        assert_eq!(
            mapped,
            f_app_list(vec![f_app_list(vec![lit(3), lit(2)]), lit(1)])
        );
        let mut visits = 0;
        assert!(t.any_fun_sym(|_| {
            visits += 1;
            true
        }));
        assert_eq!(visits, 1);
        assert!(!t.all_fun_syms(|_| {
            visits += 1;
            false
        }));
        assert_eq!(visits, 2);
        assert_eq!(count_subterms(&t, &t), 1);
        assert_eq!(count_proper_subterms(&t, &t), 0);
        assert!(!is_proper_subterm(&t, &t));
        // map_lits normalizes AC children; replacement deliberately does not.
        let ac = f_app_ac(AcSym::Xor, vec![lit(1u64), lit(2)]);
        let flip = |n: &u64| 3 - n;
        assert_eq!(map_lits(&ac, &mut |n| flip(n)), ac);
        let raw = replace_subterm(
            &mut |t| match t {
                Term::Lit(n) => lit(flip(&n)),
                t => t,
            },
            ac,
        );
        assert!(matches!(raw, Term::App(_, ref args) if args.as_ref() == [lit(2),lit(1)]));
    }

    #[test]
    fn deep_queries_mapping_and_replacement_use_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = lit(0u64);
                for _ in 0..100_000 {
                    term = f_app_list(vec![term]);
                }
                assert_eq!(term_depth(&term), 100_001);
                assert_eq!(term.size(), 100_001);
                assert!(term.all_fun_syms(|sym| *sym == FunSym::List));
                assert!(!term.any_fun_sym(|sym| *sym != FunSym::List));
                assert!(is_subterm(&lit(0), &term));
                assert_eq!(count_subterms(&lit(0), &term), 1);
                let subs = all_prot_subterms(&term);
                assert_eq!(subs.len(), 100_000);
                drop(subs);
                let mapped = map_lits(&term, &mut |n| n + 1);
                let mut visits = 0;
                let rewritten = replace_proper_subterm(
                    &mut |node| {
                        visits += 1;
                        match node {
                            Term::Lit(n) => lit(n + 1),
                            other => other,
                        }
                    },
                    term,
                );
                assert_eq!(visits, 100_000);
                assert_eq!(mapped, rewritten);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
