// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Term.Raw` from `lib/term/src/Term/Term/Raw.hs`.
//!
//! The core term datatype with its smart constructors and view types.
//! AC operators (Mult, Xor, Union, NatPlus, and user-defined AC symbols)
//! are normalised by [`f_app`]: arguments are flattened across nested
//! same-symbol applications and sorted into a canonical order.

use crate::function_symbols::{AcFctSym, AcSym, CSym, FunSym, NoEqSym};
use std::sync::Arc;

/// Diff annotation — whether the left or right interpretation of `diff` is
/// in scope.
///
/// Ported for parity with HS `Term.Term.Raw` `DiffType`; no Rust consumer
/// yet (diff-mode is not exercised by the port).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DiffType {
    Left,
    Right,
    None,
    Both,
}

/// A term over literal type `A`. Construct via [`lit`] / [`f_app`] /
/// [`f_app_no_eq`] / [`f_app_list`] — never via the variants directly,
/// because [`Term::App`] expects AC-normalised argument lists.
///
/// Children of [`Term::App`] are held in an `Arc<[_]>` so that cloning a
/// `Term` is O(1) (one atomic refcount bump) instead of a recursive deep
/// clone.  This mirrors GHC's structural sharing of term subtrees: a
/// `Term` in Haskell is a pointer-sized value shared across many sites by
/// reference, never deep-copied.  It keeps the solver's hottest allocation
/// path (`subst_system_once → Goal::clone → Fact::clone → Term::clone`)
/// off the allocator.
///
/// Reading (`args.iter()`, `args.len()`, `args[i]`, `&args[..]`) works
/// because `Arc<[_]>` derefs to `[_]`.  Construction sites convert via
/// `vec.into()` (or `Arc::from(vec)`); destructure-and-consume patterns
/// use `args.iter().cloned()` (each child clone is itself O(1)).
#[derive(Debug, Clone)]
pub enum Term<A> {
    Lit(A),
    App(FunSym, Arc<[Term<A>]>),
}

// Hand-written `Eq`/`Ord` with a structural-sharing fast-path.  `Term::App`
// children live in an `Arc<[_]>`, so two terms cloned from a common source
// (pervasive in the proof search — substitution shares subterms) point at the
// SAME slice; `Arc::ptr_eq` then settles equality/ordering in O(1) instead of a
// deep recursive walk.  The std `Ord for Arc` does NOT short-circuit on pointer
// identity (only `PartialEq` does), which is why `cmp`/`partial_cmp` are
// hand-written here.  Correctness: `Arc::ptr_eq ⇒ true` means the same
// allocation ⇒ identical contents, so the answer equals the purely
// content-based one; on a pointer mismatch we fall back to the full structural
// comparison.  Variant order (Lit < App) and field order match the derived
// impls exactly.
impl<A: PartialEq> PartialEq for Term<A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Match `self` exhaustively (no wildcard) so a new `Term` variant forces
        // an equality decision here; the inner `if let … else false` makes a
        // `Lit`/`App` cross pair unequal.
        match self {
            Term::Lit(a) => {
                if let Term::Lit(b) = other {
                    a == b
                } else {
                    false
                }
            }
            Term::App(s1, a1) => {
                if let Term::App(s2, a2) = other {
                    s1 == s2 && (Arc::ptr_eq(a1, a2) || a1[..] == a2[..])
                } else {
                    false
                }
            }
        }
    }
}
impl<A: Eq> Eq for Term<A> {}
impl<A: Ord> Ord for Term<A> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self, other) {
            (Term::Lit(a), Term::Lit(b)) => a.cmp(b),
            (Term::Lit(_), Term::App(..)) => Ordering::Less,
            (Term::App(..), Term::Lit(_)) => Ordering::Greater,
            (Term::App(s1, a1), Term::App(s2, a2)) => s1.cmp(s2).then_with(|| {
                if Arc::ptr_eq(a1, a2) {
                    Ordering::Equal
                } else {
                    a1[..].cmp(&a2[..])
                }
            }),
        }
    }
}
impl<A: PartialOrd> PartialOrd for Term<A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        match (self, other) {
            (Term::Lit(a), Term::Lit(b)) => a.partial_cmp(b),
            (Term::Lit(_), Term::App(..)) => Some(Ordering::Less),
            (Term::App(..), Term::Lit(_)) => Some(Ordering::Greater),
            (Term::App(s1, a1), Term::App(s2, a2)) => match s1.partial_cmp(s2) {
                Some(Ordering::Equal) => {
                    if Arc::ptr_eq(a1, a2) {
                        Some(Ordering::Equal)
                    } else {
                        a1[..].partial_cmp(&a2[..])
                    }
                }
                non_eq => non_eq,
            },
        }
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
        match self {
            Term::Lit(a) => {
                0u8.hash(state);
                a.hash(state);
            }
            Term::App(s, args) => {
                1u8.hash(state);
                s.hash(state);
                args.hash(state);
            }
        }
    }
}

/// Mirror view that distinguishes the two cases — kept for parity with the
/// Haskell `TermView`. Since Rust's `match` already lets you destructure
/// `Term::Lit`/`Term::App` directly, this is mostly here for documentation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermView<'a, A> {
    Lit(&'a A),
    App(&'a FunSym, &'a [Term<A>]),
}

impl<A> Term<A> {
    pub fn view(&self) -> TermView<'_, A> {
        match self {
            Term::Lit(l) => TermView::Lit(l),
            Term::App(s, ts) => TermView::App(s, ts),
        }
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

// =============================================================================
// Subterm tests / counts
// =============================================================================

pub fn is_subterm<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> bool {
    if needle == haystack {
        return true;
    }
    is_proper_subterm(needle, haystack)
}

pub fn is_proper_subterm<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> bool {
    match haystack {
        Term::App(_, ts) => ts.iter().any(|t| is_subterm(needle, t)),
        Term::Lit(_) => false,
    }
}

pub fn count_subterms<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> usize {
    if needle == haystack {
        return 1;
    }
    count_proper_subterms(needle, haystack)
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
    match t {
        Term::App(_, args) if is_pair(t) || is_ac(t) => {
            args.iter().flat_map(|a| all_prot_subterms(a)).collect()
        }
        Term::App(_, args) => {
            let mut out = vec![t.clone()];
            for a in args.iter() {
                out.extend(all_prot_subterms(a));
            }
            out
        }
        Term::Lit(_) => Vec::new(),
    }
}

// =============================================================================
// Replacement helpers (top-down)
// =============================================================================

pub fn replace_subterm<A: Clone, F: FnMut(Term<A>) -> Term<A>>(f: &mut F, t: Term<A>) -> Term<A> {
    let new = f(t);
    match new {
        Term::Lit(_) => new,
        Term::App(s, ts) => {
            let new_ts: Vec<Term<A>> = ts.iter().cloned().map(|c| replace_subterm(f, c)).collect();
            Term::App(s, new_ts.into())
        }
    }
}

pub fn replace_proper_subterm<A: Clone, F: FnMut(Term<A>) -> Term<A>>(
    f: &mut F,
    t: Term<A>,
) -> Term<A> {
    match t {
        Term::App(s, ts) => {
            let new_ts: Vec<Term<A>> = ts.iter().cloned().map(|c| replace_subterm(f, c)).collect();
            Term::App(s, new_ts.into())
        }
        Term::Lit(_) => t,
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
        match self {
            Term::Lit(a) => a.size(),
            Term::App(_, ts) => ts.iter().map(|t| t.size()).sum::<usize>() + 1,
        }
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
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{exp_sym, pair_sym, AcSym, CSym, FunSym};

    /// The pinned submodule's `lib/term/src/Term/Term/Raw.hs`, embedded at
    /// build time.
    const RAW_HS: &str = include_str!("../../../tamarin-prover/lib/term/src/Term/Term/Raw.hs");

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
            assert!(Arc::ptr_eq(a, b));
            assert!(!Arc::ptr_eq(a, c));
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
}
