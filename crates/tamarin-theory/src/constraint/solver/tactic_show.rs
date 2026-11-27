// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! `show`-faithful renderers and the shared `checkFormula` engine for the
//! Vacarme/noise tactic selectors (`dhreNoise`, `defaultNoise`,
//! `reasonableNoncesNoise`, `nonAbsurdConstraint`, `isFactName`,
//! `isInFactTerms`).
//!
//! Port of the `tacticFunctions` where-clause in
//! `lib/theory/src/Theory/Text/Parser/Tactics.hs`.
//!
//! These selectors build PCRE patterns from `map show <LVar>` and test
//! `show <term> =~ ...`.  They use Haskell's `Show` instances, which are
//! NOT the same as the user-facing pretty-printer:
//!   - `show LVar`  : `sortPrefix s ++ body`  (LTerm.hs)
//!   - `show Name`  : `~'n'` / `'n'` / `#'n'` / `%'n'` (LTerm.hs)
//!   - `show (Term a)` (raw form, Term/Term/Raw.hs): prefix
//!     applications whose arguments are separated by a bare comma, a `NoEq` or
//!     user-`AC` symbol alone when it takes no arguments, and the derived
//!     `ACSym` constructor name (Union/Mult/Xor/NatPlus) as the head of a
//!     builtin AC application.  [`tamarin_term::term::show_term`] is that
//!     instance.
//!   - `show (BVar v)` (derived, LTerm.hs): `Bound i` / `Free <show v>`.
//!
//! `show (Term (Lit Name (BVar LVar)))` (the `VTerm Name (BVar LVar)` used by
//! `checkFormula`) therefore renders Var leaves as `Bound i` / `Free <lvar>`.

use tamarin_term::lterm::LVar;
use tamarin_term::term::show_term;

use crate::atom::ProtoAtom;
use crate::fact::Fact;
use crate::formula::BLNTerm;
use crate::guarded::Guarded;

// =============================================================================
// checkFormula — the shared engine (Tactics.hs)
// =============================================================================

/// Recursively collect ALL action fact-tag names occurring in the guards of
/// a guarded formula.  Mirrors HS `guardFactTags` (Guarded.hs),
/// which folds over the WHOLE structure (not just the top level).
fn guard_fact_tag_names(g: &Guarded, out: &mut Vec<String>) {
    match g {
        Guarded::Atom(_) => {}
        Guarded::Disj(xs) | Guarded::Conj(xs) => {
            for x in xs.iter() {
                guard_fact_tag_names(x, out);
            }
        }
        Guarded::GGuarded { guards, body, .. } => {
            for a in guards.iter() {
                if let ProtoAtom::Action(_, f) = a {
                    out.push(crate::fact::fact_tag_name(&f.tag));
                }
            }
            guard_fact_tag_names(body, out);
        }
    }
}

/// HS `getFormulaTerms` (Tactics.hs): the fact terms of the single
/// top-level guard, when the formula is exactly `GGuarded _ _ [Action _ fa] _`.
fn formula_action_fact(g: &Guarded) -> Option<&Fact<BLNTerm>> {
    if let Guarded::GGuarded { guards, .. } = g
        && guards.len() == 1
        && let ProtoAtom::Action(_, fa) = &guards[0]
    {
        return Some(fa);
    }
    None
}

/// HS `checkFormula oracleType f` (Tactics.hs).
///
/// Returns the free `LVar`s of the top-level Reveal-action's fact terms,
/// but ONLY if (a) some guard fact-tag name matches the regex `"Reveal"`
/// AND (b) `show (getFormulaTerms f)` matches `"exp\\('g'"`
/// (or `"grpid,exp\\('g'"` when `oracleType == "curve"`).
///
/// The returned `VarSpec`s are `show`n by the callers to build PCRE
/// alternations like `(~n|~s|...)`.
fn check_formula(oracle_type: &str, f: &Guarded) -> Vec<LVar> {
    // rev = any guard fact-tag name =~ "Reveal"
    let mut tag_names = Vec::new();
    guard_fact_tag_names(f, &mut tag_names);
    if !tag_names.iter().any(|n| n.contains("Reveal")) {
        return Vec::new();
    }

    // expG = show (getFormulaTerms f) =~ <pattern>
    // getFormulaTerms returns the top-level Action fact's term args, shown
    // as a Haskell list `[t1,t2,..]`.
    let fact = match formula_action_fact(f) {
        Some(fa) => fa,
        None => return Vec::new(),
    };
    let shown_terms = show_term_list(fact.terms());
    let pat = if oracle_type == "curve" {
        "grpid,exp\\('g'"
    } else {
        "exp\\('g'"
    };
    let exp_g = super::goals::regex_is_match(pat, &shown_terms);
    if !exp_g {
        return Vec::new();
    }

    // getFormulaTermsCore (Tactics.hs):
    //   concat $ map (map getCore . varsVTerm) (fact args)
    // HS `varsVTerm` (VTerm.hs) sortednubs over `Ord (BVar LVar)`
    // (Bound < Free), collecting BOTH Bound and Free vars; `getCore`
    // then maps `Free v -> v` and `error`s on any Bound de-Bruijn index.
    // We collect only Free vars per term (sortednub: sorted + deduped), then
    // concat.  This is byte-identical to HS whenever HS does not crash; a Bound
    // var here would require an existentially-quantified Reveal action whose
    // fact TERM still carries an unbound de-Bruijn index (the corpus's Reveal
    // formulas quantify only the temporal #reveal, so me/re/peer are Free).
    // Dropping the Bound (vs. matching HS's panic) is intentional: a crash is
    // never the desired `--prove` output.
    let mut acc: Vec<LVar> = Vec::new();
    for arg in fact.terms().iter() {
        // `varsVTerm` is `sortednub` over `Ord (BVar LVar)`; `frees` is that
        // sorted, deduplicated walk restricted to the `Free` leaves.
        acc.extend(tamarin_term::lterm::frees(arg));
    }
    acc
}

/// HS `show [VTerm Name (BVar LVar)]` — the derived `Show [a]`:
/// `"[" ++ intercalate "," (map show xs) ++ "]"`.
fn show_term_list(args: &[BLNTerm]) -> String {
    let mut out = String::from("[");
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&show_term(a));
    }
    out.push(']');
    out
}

/// The set of `show`n LVars from `concat (map (checkFormula o) sFormulas)`.
pub fn sys_reveal_shown(oracle_type: &str, formulas: &[std::sync::Arc<Guarded>]) -> Vec<String> {
    let mut out = Vec::new();
    for f in formulas {
        for v in check_formula(oracle_type, f) {
            out.push(v.to_string());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::{exp_sym, nat_one_sym, AcSym};
    use tamarin_term::lterm::{BVar, LNTerm, LSort, Name, NameTag};
    use tamarin_term::term::{f_app_ac, f_app_no_eq};
    use tamarin_term::vterm::{const_term, var_term};

    fn fresh(name: &str) -> BLNTerm {
        var_term(BVar::Free(LVar::new(name, LSort::Fresh, 0)))
    }

    fn pub_name(name: &str) -> BLNTerm {
        const_term(Name::new(NameTag::Pub, name))
    }

    /// `show LVar` is `sortPrefix s ++ body`.  Each sort has one prefix; Msg
    /// has none.  The `.idx` suffix appears only for an index that is not
    /// zero.
    #[test]
    fn show_lvar_covers_every_sort_prefix_and_the_index_suffix() {
        let sorted = |sort, name: &str, idx| LVar::new(name, sort, idx).to_string();
        assert_eq!(sorted(LSort::Fresh, "s", 0), "~s");
        assert_eq!(sorted(LSort::Pub, "a", 0), "$a");
        assert_eq!(sorted(LSort::Node, "i", 0), "#i");
        assert_eq!(sorted(LSort::Nat, "n", 0), "%n");
        assert_eq!(sorted(LSort::Msg, "m", 0), "m");
        // An index that is not zero appends `.idx`.  A variable with no name
        // shows the index alone.
        assert_eq!(sorted(LSort::Fresh, "s", 3), "~s.3");
        assert_eq!(sorted(LSort::Msg, "", 7), "7");
    }

    /// The derived `Show [a]` puts the items in brackets.  It separates them
    /// with a comma and no space.  It shows `[]` for an empty list.
    #[test]
    fn show_term_list_matches_exp_g() {
        let t: BLNTerm = f_app_no_eq(exp_sym(), vec![pub_name("g"), fresh("s")]);
        assert_eq!(
            show_term_list(std::slice::from_ref(&t)),
            "[exp('g',Free ~s)]"
        );
        assert_eq!(
            show_term_list(&[t.clone(), f_app_no_eq(nat_one_sym(), vec![])]),
            "[exp('g',Free ~s),tone]"
        );
        assert_eq!(show_term_list(&[]), "[]");
    }

    /// `Show (Term a)` (Term/Raw.hs) over every applied-symbol arm: the
    /// `NoEq` nullary/applied pair (including `one` and `tone`,
    /// FunctionSymbols.hs), `C EMap`, `List`, the four builtin AC operators
    /// (whose derived `show ACSym` names always take an argument list), the
    /// user-`[AC]` nullary/applied pair, and a `Bound` leaf (derived
    /// `Show (BVar v)`, LTerm.hs).  An application intercalates its WHOLE
    /// argument list, so a three-argument AC term shows flat.
    #[test]
    fn show_term_covers_every_applied_symbol_arm() {
        use tamarin_term::builtin::{emap, msg_var, mult, nat_plus, union, xor};
        use tamarin_term::function_symbols::{
            one_sym, AcFctSym, Constructability, FunSym, NdcState, NoEqSym, Privacy,
        };
        use tamarin_term::term::{f_app_acfct, f_app_list, Term};

        let (x, y) = (msg_var("x", 0), msg_var("y", 0));
        let noeq = |n: &[u8], a: usize| {
            NoEqSym::new(
                n.to_vec(),
                a,
                Privacy::Public,
                Constructability::Constructor,
            )
        };
        let acfct = |n: &[u8]| {
            AcFctSym::new(
                n.to_vec(),
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            )
        };
        let xy = || vec![x.clone(), y.clone()];
        // `FApp (AC (ACfct (s,_))) [] -> s`: the bare name, no parens.
        let nullary_acfct: LNTerm =
            Term::App(FunSym::Ac(AcSym::AcFct(acfct(b"nil"))), Vec::new().into());
        let exp_g: BLNTerm = f_app_no_eq(exp_sym(), vec![pub_name("g"), fresh("s")]);
        let mult3: BLNTerm = f_app_ac(AcSym::Mult, vec![fresh("a"), fresh("b"), fresh("c")]);
        let nullary = |sym| -> LNTerm { f_app_no_eq(sym, vec![]) };
        let bound: BLNTerm = var_term(BVar::Bound(3));
        let rows = [
            (show_term(&nullary(noeq(b"g", 0))), "g"),
            (show_term(&f_app_no_eq(noeq(b"h", 2), xy())), "h(x,y)"),
            (show_term(&nullary(one_sym())), "one"),
            (show_term(&nullary(nat_one_sym())), "tone"),
            (show_term(&exp_g), "exp('g',Free ~s)"),
            (show_term(&emap(x.clone(), y.clone())), "em(x,y)"),
            (show_term(&f_app_list(xy())), "LIST(x,y)"),
            (show_term(&union(x.clone(), y.clone())), "Union(x,y)"),
            (show_term(&mult(x.clone(), y.clone())), "Mult(x,y)"),
            (show_term(&mult3), "Mult(Free ~a,Free ~b,Free ~c)"),
            (show_term(&xor(x.clone(), y.clone())), "Xor(x,y)"),
            (show_term(&nat_plus(x.clone(), y.clone())), "NatPlus(x,y)"),
            (show_term(&f_app_acfct(acfct(b"xorr"), xy())), "xorr(x,y)"),
            (show_term(&nullary_acfct), "nil"),
            (show_term(&bound), "Bound 3"),
        ];
        for (shown, expected) in rows {
            assert_eq!(shown, expected);
        }
    }
}
