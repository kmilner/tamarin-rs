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
        let mut pending =
            tamarin_utils::drop_stack::DropStack::from(std::mem::take(&mut self.0).into_vec());
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
        let _: std::ops::ControlFlow<()> = walk_terms(std::slice::from_ref(self), |node| {
            match node {
                Term::Lit(a) => {
                    0u8.hash(state);
                    a.hash(state);
                }
                Term::App(s, args) => {
                    1u8.hash(state);
                    s.hash(state);
                    args.len().hash(state);
                }
            }
            std::ops::ControlFlow::Continue(true)
        });
    }
}

impl<A: std::fmt::Debug> std::fmt::Debug for Term<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        tamarin_utils::stack::bounded_debug(self, f, |f| {
            if let Term::Lit(a) = self {
                return f.debug_tuple("Lit").field(a).finish();
            }
            if f.alternate() {
                // Keep standard formatting within the shared pretty-depth budget.
                // Deeper subtrees use the compact worklist below; traversal guards
                // alone cannot protect Rust's recursive indentation writers.
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
        })
    }
}

/// Preorder traversal shared by read-only queries. `Continue(false)` prunes a
/// matched subtree; `Break` short-circuits without visiting later siblings.
pub fn walk_terms<'a, A, B>(
    roots: &'a [Term<A>],
    mut visit: impl FnMut(&'a Term<A>) -> std::ops::ControlFlow<B, bool>,
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
    fold_term(t, f, &mut f_app)
}

/// Fold original children left to right before their application. Replacements
/// returned by either callback are inserted once, without traversing them.
pub fn fold_term<A, B>(
    t: &Term<A>,
    literal: &mut dyn FnMut(&A) -> Term<B>,
    application: &mut impl FnMut(FunSym, Vec<Term<B>>) -> Term<B>,
) -> Term<B> {
    let mut current = t;
    let mut pending = Vec::new();
    loop {
        let mut result = match current {
            Term::Lit(a) => literal(a),
            Term::App(sym, args) => {
                let mut children = args.iter();
                if let Some(first) = children.next() {
                    pending.push((*sym, children, Vec::with_capacity(args.len())));
                    current = first;
                    continue;
                }
                application(*sym, Vec::new())
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
            result = application(sym, mapped);
        }
    }
}

/// Rewrite a term top-down without using the native call stack.
///
/// `replace` is called before a node's children are visited. Returning a term
/// replaces that complete subtree, so the replacement and the original
/// children are not visited. Every visited application is passed to `rebuild`.
pub fn rewrite_term<A: Clone>(
    t: &Term<A>,
    replace: &mut impl FnMut(&Term<A>) -> Option<Term<A>>,
    rebuild: &mut impl FnMut(FunSym, Vec<Term<A>>) -> Term<A>,
) -> Term<A> {
    rewrite_term_impl(t, replace, rebuild, true).unwrap_or_else(|| t.clone())
}

/// Top-down rewrite which rebuilds applications only along changed paths.
/// An unchanged subtree is returned with an O(1) clone.
pub fn rewrite_term_cow<A: Clone>(
    t: &Term<A>,
    replace: &mut impl FnMut(&Term<A>) -> Option<Term<A>>,
    rebuild: &mut impl FnMut(FunSym, Vec<Term<A>>) -> Term<A>,
) -> Term<A> {
    rewrite_term_impl(t, replace, rebuild, false).unwrap_or_else(|| t.clone())
}

fn rewrite_term_impl<A: Clone>(
    t: &Term<A>,
    replace: &mut impl FnMut(&Term<A>) -> Option<Term<A>>,
    rebuild: &mut impl FnMut(FunSym, Vec<Term<A>>) -> Term<A>,
    rebuild_unchanged: bool,
) -> Option<Term<A>> {
    if let Some(replacement) = replace(t) {
        return Some(replacement);
    }
    let Term::App(sym, args) = t else {
        return None;
    };
    if args.is_empty() {
        return if rebuild_unchanged {
            Some(rebuild(*sym, Vec::new()))
        } else {
            None
        };
    }

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
    let mut parents = Vec::new();
    loop {
        let changed = match frame.children.next() {
            Some(child) => {
                if let Some(replacement) = replace(child) {
                    Some(replacement)
                } else {
                    match child {
                        Term::App(_, args) if !args.is_empty() => {
                            parents.push(frame);
                            frame = Frame {
                                term: child,
                                children: args.iter(),
                                mapped: None,
                            };
                            continue;
                        }
                        Term::App(sym, _) if rebuild_unchanged => Some(rebuild(*sym, Vec::new())),
                        _ => None,
                    }
                }
            }
            None => {
                let result = if let Some(mapped) = frame.mapped.take() {
                    let Term::App(sym, _) = frame.term else {
                        unreachable!()
                    };
                    Some(rebuild(*sym, mapped))
                } else if rebuild_unchanged {
                    let Term::App(sym, args) = frame.term else {
                        unreachable!()
                    };
                    Some(rebuild(*sym, args.to_vec()))
                } else {
                    None
                };
                let Some(parent) = parents.pop() else {
                    return result;
                };
                frame = parent;
                result
            }
        };

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

/// Replace literals once, normalizing only applications with changed children.
/// `None` preserves the original subtree; a flat application needs no worklist
/// allocation, and argument vectors are allocated only on the first change.
pub fn bind_lits_cow<A: Ord + Clone>(
    t: &Term<A>,
    f: &mut impl FnMut(&A) -> Option<Term<A>>,
) -> Option<Term<A>> {
    bind_lits_cow_with_order(t, f, false)
}

// Monotone free-variable renaming preserves the existing argument order;
// ordinary substitutions rebuild through the normalizing constructor.
pub(crate) fn bind_lits_cow_with_order<A: Ord + Clone>(
    t: &Term<A>,
    f: &mut impl FnMut(&A) -> Option<Term<A>>,
    preserve_order: bool,
) -> Option<Term<A>> {
    rewrite_term_impl(
        t,
        &mut |term| match term {
            Term::Lit(literal) => f(literal),
            Term::App(..) => None,
        },
        &mut |sym, mapped| {
            if preserve_order {
                unsafe_f_app(sym, mapped)
            } else {
                f_app(sym, mapped)
            }
        },
        false,
    )
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
                    tamarin_utils::stack::ensure_sufficient_stack(|| write_show_term(a, out));
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
#[path = "term_tests.rs"]
mod tests;

#[cfg(test)]
mod iterative_operations_tests {
    use super::*;
    use std::hash::{Hash, Hasher};

    #[test]
    fn deep_alternate_debug_uses_small_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            let mut term = Term::Lit(42u64);
            for _ in 0..8192 {
                term = f_app_list(vec![term]);
            }
            let text = format!("{term:#?}");
            assert_eq!(text.matches("App(").count(), 8192);
            assert!(text.contains("Lit(42)"));
        });
    }

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
        tamarin_test_support::on_stack(256 * 1024, || {
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
        });
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
    fn top_down_rewrite_prunes_replacements_and_preserves_unchanged_storage() {
        let hidden = f_app_list(vec![lit(1u64), lit(2)]);
        let term = f_app_list(vec![hidden.clone(), lit(3)]);
        let mut visited_literals = Vec::new();
        let replaced = rewrite_term(
            &term,
            &mut |node| {
                if node == &hidden {
                    return Some(lit(9));
                }
                if let Term::Lit(value) = node {
                    visited_literals.push(*value);
                }
                None
            },
            &mut unsafe_f_app,
        );
        assert_eq!(visited_literals, [3]);
        assert_eq!(replaced, f_app_list(vec![lit(9), lit(3)]));

        let unchanged = rewrite_term_cow(&term, &mut |_| None, &mut unsafe_f_app);
        let (Term::App(_, old_args), Term::App(_, new_args)) = (&term, &unchanged) else {
            unreachable!()
        };
        assert_eq!(old_args.as_ptr(), new_args.as_ptr());

        let raw = Term::App(
            FunSym::List,
            vec![Term::App(FunSym::List, Vec::<Term<u64>>::new().into())].into(),
        );
        let mut rebuilt = 0;
        rewrite_term(&raw, &mut |_| None, &mut |sym, args| {
            rebuilt += 1;
            unsafe_f_app(sym, args)
        });
        assert_eq!(rebuilt, 2);
    }

    #[test]
    fn deep_queries_mapping_and_replacement_use_bounded_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
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
        });
    }
}
