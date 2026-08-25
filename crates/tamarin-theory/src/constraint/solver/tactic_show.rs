// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `show`-faithful renderers and the shared `checkFormula` engine for the
//! Vacarme/noise tactic selectors (`dhreNoise`, `defaultNoise`,
//! `reasonableNoncesNoise`, `nonAbsurdConstraint`, `isFactName`,
//! `isInFactTerms`).
//!
//! Port of the `tacticFunctions` where-clause in
//! `lib/theory/src/Theory/Text/Parser/Tactics.hs:117-220`.
//!
//! These selectors build PCRE patterns from `map show <LVar>` and test
//! `show <term> =~ ...`.  They use Haskell's `Show` instances, which are
//! NOT the same as the user-facing pretty-printer:
//!   - `show LVar`  : `sortPrefix s ++ body`  (LTerm.hs:550-557)
//!   - `show Name`  : `~'n'` / `'n'` / `#'n'` / `%'n'` (LTerm.hs:235-240)
//!   - `show (Term a)` (raw form, Term/Term/Raw.hs:227-237): prefix
//!     applications whose arguments are separated by a bare comma, a `NoEq` or
//!     user-`AC` symbol alone when it takes no arguments, and the derived
//!     `ACSym` constructor name (Union/Mult/Xor/NatPlus) as the head of a
//!     builtin AC application.  [`tamarin_term::term::show_term`] is that
//!     instance.
//!   - `show (BVar v)` (derived, LTerm.hs:476-478): `Bound i` / `Free <show v>`.
//!
//! `show (Term (Lit Name (BVar LVar)))` (the `VTerm Name (BVar LVar)` used by
//! `checkFormula`) therefore renders Var leaves as `Bound i` / `Free <lvar>`.

use tamarin_term::lterm::{LNTerm, LVar};
use tamarin_term::term::show_term;

use crate::atom::ProtoAtom;
use crate::fact::{Fact, FactTag, Multiplicity};
use crate::formula::BLNTerm;
use crate::guarded::Guarded;

// =============================================================================
// `show FactTag` (derived Show, Theory/Model/Fact.hs:136-149) — used by isFactName
// =============================================================================

/// HS derived `show FactTag`.  For `ProtoFact m n a` this is
/// `ProtoFact <show m> "<n>" <a>` (with the multiplicity constructor name
/// and the Haskell-quoted/escaped string literal).
pub fn show_fact_tag(t: &FactTag) -> String {
    match t {
        FactTag::Proto(m, n, a) => {
            let mult = match m {
                Multiplicity::Persistent => "Persistent",
                Multiplicity::Linear => "Linear",
            };
            format!("ProtoFact {} {} {}", mult, show_haskell_string(n), a)
        }
        FactTag::Fresh => "FreshFact".into(),
        FactTag::Out => "OutFact".into(),
        FactTag::In => "InFact".into(),
        FactTag::Ku => "KUFact".into(),
        FactTag::Kd => "KDFact".into(),
        FactTag::Ded => "DedFact".into(),
        FactTag::Term => "TermFact".into(),
    }
}

/// Haskell's `show :: String -> String` (the `Show String` instance):
/// surrounds with double-quotes and escapes the standard control/quote
/// characters.  Protocol fact names are plain identifiers so the common
/// case is just `"<name>"`, but we escape to stay faithful.
fn show_haskell_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

// =============================================================================
// checkFormula — the shared engine (Tactics.hs:190-209)
// =============================================================================

/// Recursively collect ALL action fact-tag names occurring in the guards of
/// a guarded formula.  Mirrors HS `guardFactTags` (Guarded.hs:167-174),
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

/// HS `getFormulaTerms` (Tactics.hs:203-205): the fact terms of the single
/// top-level guard, when the formula is exactly `GGuarded _ _ [Action _ fa] _`.
fn formula_action_fact(g: &Guarded) -> Option<&Fact<BLNTerm>> {
    if let Guarded::GGuarded { guards, .. } = g {
        if guards.len() == 1 {
            if let ProtoAtom::Action(_, fa) = &guards[0] {
                return Some(fa);
            }
        }
    }
    None
}

/// HS `checkFormula oracleType f` (Tactics.hs:190-209).
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
    let shown_terms = show_term_list(&fact.terms);
    let pat = if oracle_type == "curve" {
        "grpid,exp\\('g'"
    } else {
        "exp\\('g'"
    };
    let exp_g = super::goals::regex_is_match(pat, &shown_terms);
    if !exp_g {
        return Vec::new();
    }

    // getFormulaTermsCore (Tactics.hs:207-209):
    //   concat $ map (map getCore . varsVTerm) (fact args)
    // HS `varsVTerm` (VTerm.hs:116-117) sortednubs over `Ord (BVar LVar)`
    // (Bound < Free), collecting BOTH Bound and Free vars; `getCore` (:194-195)
    // then maps `Free v -> v` and `error`s on any Bound de-Bruijn index.
    // We collect only Free vars per term (sortednub: sorted + deduped), then
    // concat.  This is byte-identical to HS whenever HS does not crash; a Bound
    // var here would require an existentially-quantified Reveal action whose
    // fact TERM still carries an unbound de-Bruijn index (the corpus's Reveal
    // formulas quantify only the temporal #reveal, so me/re/peer are Free).
    // Dropping the Bound (vs. matching HS's panic) is intentional: a crash is
    // never the desired `--prove` output.
    let mut acc: Vec<LVar> = Vec::new();
    for arg in fact.terms.iter() {
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

/// HS `getFactTerms_ goal` for `reasonableNoncesNoise` (Tactics.hs:184-186):
/// the fact terms of an `ActionG _ (Fact { factTerms = ft })`, else `[]`.
pub fn action_goal_fact_terms(goal: &crate::constraint::constraints::Goal) -> Vec<LNTerm> {
    if let crate::constraint::constraints::Goal::Action(_, fa) = goal {
        fa.terms.to_vec()
    } else {
        Vec::new()
    }
}

/// Accessor for the single-term action fact used by `isInFactTerms`
/// (Tactics.hs:218-220): `ActionG _ (Fact { factTerms = [test] })`.
pub fn action_goal_single_term(goal: &crate::constraint::constraints::Goal) -> Option<&LNTerm> {
    if let crate::constraint::constraints::Goal::Action(_, fa) = goal {
        if fa.terms.len() == 1 {
            return Some(&fa.terms[0]);
        }
    }
    None
}

/// Accessor pair for `isFactName` (Tactics.hs:212-215).  Returns either the
/// linear ProtoFact NAME (premise case) or the `show FactTag` (action case).
pub enum FactNameProbe {
    /// `PremiseG _ Fact{factTag = ProtoFact Linear name _}` => compare `name == s`.
    PremiseLinearName(String),
    /// `ActionG _ (Fact{factTag = tag})` => compare `show tag == s`.
    ActionShowTag(String),
    /// Neither pattern matches.
    None,
}

pub fn fact_name_probe(goal: &crate::constraint::constraints::Goal) -> FactNameProbe {
    use crate::constraint::constraints::Goal;
    match goal {
        Goal::Premise(_, fa) => {
            if let FactTag::Proto(Multiplicity::Linear, name, _) = &fa.tag {
                FactNameProbe::PremiseLinearName(name.to_string())
            } else {
                FactNameProbe::None
            }
        }
        Goal::Action(_, fa) => FactNameProbe::ActionShowTag(show_fact_tag(&fa.tag)),
        _ => FactNameProbe::None,
    }
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
    use tamarin_term::lterm::{BVar, LSort, Name, NameTag};
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

    #[test]
    fn show_term_writes_exp_g() {
        // 'g'^~s  ==>  exp('g',Free ~s)
        let t: BLNTerm = f_app_no_eq(exp_sym(), vec![pub_name("g"), fresh("s")]);
        assert_eq!(show_term(&t), "exp('g',Free ~s)");
    }

    /// HS's `Show (Term a)` intercalates the WHOLE argument list of an
    /// application (Term/Term/Raw.hs:227-237), so a three-argument AC term
    /// shows flat rather than as a nested binary chain.
    #[test]
    fn show_term_writes_a_three_argument_ac_application_flat() {
        let t: BLNTerm = f_app_ac(AcSym::Mult, vec![fresh("a"), fresh("b"), fresh("c")]);
        assert_eq!(show_term(&t), "Mult(Free ~a,Free ~b,Free ~c)");
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

    /// Every arm of the derived `Show FactTag`.  `isFactName` compares
    /// against this string, and `jgnFactName` writes it out.  A constructor
    /// with a wrong spelling therefore breaks both the tactic matching and
    /// `--output-json`, and nothing reports an error.
    #[test]
    fn show_fact_tag_covers_every_derived_show_arm() {
        assert_eq!(
            show_fact_tag(&FactTag::Proto(Multiplicity::Linear, "Foo", 2)),
            "ProtoFact Linear \"Foo\" 2"
        );
        assert_eq!(
            show_fact_tag(&FactTag::Proto(Multiplicity::Persistent, "Foo", 0)),
            "ProtoFact Persistent \"Foo\" 0"
        );
        assert_eq!(show_fact_tag(&FactTag::Fresh), "FreshFact");
        assert_eq!(show_fact_tag(&FactTag::Out), "OutFact");
        assert_eq!(show_fact_tag(&FactTag::In), "InFact");
        assert_eq!(show_fact_tag(&FactTag::Ku), "KUFact");
        assert_eq!(show_fact_tag(&FactTag::Kd), "KDFact");
        assert_eq!(show_fact_tag(&FactTag::Ded), "DedFact");
        assert_eq!(show_fact_tag(&FactTag::Term), "TermFact");
    }

    /// Every applied-symbol arm of `Show (Term a)` (Term/Raw.hs:227-237):
    /// the `NoEq` nullary/applied pair, `C EMap`, `List`, the four builtin
    /// AC operators (whose derived `show ACSym` names always take an
    /// argument list) and the user-`[AC]` nullary/applied pair.
    #[test]
    fn show_term_covers_every_applied_symbol_arm() {
        use tamarin_term::builtin::{emap, msg_var, mult, nat_plus, union, xor};
        use tamarin_term::function_symbols::{
            AcFctSym, Constructability, NdcState, NoEqSym, Privacy,
        };
        use tamarin_term::term::{f_app_acfct, f_app_list, f_app_no_eq};

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

        let nullary: LNTerm = f_app_no_eq(noeq(b"g", 0), vec![]);
        assert_eq!(show_term(&nullary), "g");
        assert_eq!(
            show_term(&f_app_no_eq(noeq(b"h", 2), vec![x.clone(), y.clone()])),
            "h(x,y)"
        );
        assert_eq!(show_term(&emap(x.clone(), y.clone())), "em(x,y)");
        assert_eq!(
            show_term(&f_app_list(vec![x.clone(), y.clone()])),
            "LIST(x,y)"
        );
        assert_eq!(show_term(&union(x.clone(), y.clone())), "Union(x,y)");
        assert_eq!(show_term(&mult(x.clone(), y.clone())), "Mult(x,y)");
        assert_eq!(show_term(&xor(x.clone(), y.clone())), "Xor(x,y)");
        assert_eq!(show_term(&nat_plus(x.clone(), y.clone())), "NatPlus(x,y)");
        assert_eq!(
            show_term(&f_app_acfct(acfct(b"xorr"), vec![x.clone(), y.clone()])),
            "xorr(x,y)"
        );
        // `FApp (AC (ACfct (s,_))) [] -> s` — the bare name, no parens.
        let nullary_acfct: LNTerm = tamarin_term::term::Term::App(
            tamarin_term::function_symbols::FunSym::Ac(AcSym::AcFct(acfct(b"nil"))),
            Vec::new().into(),
        );
        assert_eq!(show_term(&nullary_acfct), "nil");
    }

    #[test]
    fn show_term_writes_the_two_nullary_arithmetic_symbols_by_name() {
        // fAppOne = FApp (NoEq oneSym) [] with oneSymString = "one" and
        // fAppNatOne = FApp (NoEq natOneSym) [] with natOneSymString = "tone"
        // (FunctionSymbols.hs:226,236,255,267).
        let one: BLNTerm = f_app_no_eq(tamarin_term::function_symbols::one_sym(), vec![]);
        assert_eq!(show_term(&one), "one");
        let tone: BLNTerm = f_app_no_eq(nat_one_sym(), vec![]);
        assert_eq!(show_term(&tone), "tone");
    }

    /// A `Bound` leaf shows as the derived `Show (BVar v)` writes it
    /// (LTerm.hs:476-478).
    #[test]
    fn show_term_writes_a_bound_leaf_with_its_index() {
        let t: BLNTerm = var_term(BVar::Bound(3));
        assert_eq!(show_term(&t), "Bound 3");
    }
}
