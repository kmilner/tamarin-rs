// Currently GPL 3.0 until granted permission by the following authors:
//   racoucho1u, meiersi, jdreier, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/term/src/Term/Term/Raw.hs, lib/term/src/Term/VTerm.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Tactics.hs

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
//!   - `show LVar`  : `sortPrefix s ++ body`  (LTerm.hs:526-533)
//!   - `show Name`  : `~'n'` / `'n'` / `#'n'` / `%'n'` (LTerm.hs:231-235)
//!   - `show (Term a)` (raw form, Term/Raw.hs:219-227):
//!     ```text
//!     Lit l                -> show l
//!     FApp (NoEq (s,_)) [] -> s
//!     FApp (NoEq (s,_)) as -> s ++ "(" ++ intercalate "," (map show as) ++ ")"
//!     FApp (C EMap)     as -> "em" ++ "(" ++ ... ++ ")"
//!     FApp List         as -> "LIST" ++ "(" ++ ... ++ ")"
//!     FApp (AC o)       as -> show o ++ "(" ++ ... ++ ")"
//!     ```
//!     where `show o` is the AC constructor name (Union/Mult/Xor/NatPlus).
//!   - `show (BVar v)` (derived, LTerm.hs:452-454): `Bound i` / `Free <show v>`.
//!
//! `show (Term (Lit Name (BVar LVar)))` (the `VTerm Name (BVar LVar)` used by
//! `checkFormula`) therefore renders Var leaves as `Bound i` / `Free <lvar>`.

use tamarin_parser::ast as p;
use tamarin_term::function_symbols::{AcSym, CSym, FunSym};
use tamarin_term::lterm::{LNTerm, Name, NameTag};
use tamarin_term::vterm::Lit;

use crate::fact::{FactTag, Multiplicity};
use crate::guarded::Guarded;
use crate::guarded_types::{BVar, GAtom, GFact, GTerm};

// =============================================================================
// `show` of a free LVar carried in a GTerm (`p::VarSpec`)
// =============================================================================

/// HS `show LVar` (LTerm.hs:526-533): `sortPrefix s ++ body`.
pub(crate) fn show_varspec(v: &p::VarSpec) -> String {
    let mut s = String::new();
    write_varspec(v, &mut s);
    s
}

/// Like [`show_varspec`] but writes directly into `out`, avoiding the
/// throwaway intermediate `String`.  Produces byte-identical output.
fn write_varspec(v: &p::VarSpec, out: &mut String) {
    let prefix = match v.sort {
        p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => "~",
        p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => "$",
        p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => "#",
        p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => "%",
        // Msg / Untagged / Suffix(Msg) => "" (LSortMsg has no prefix).
        _ => "",
    };
    out.push_str(prefix);
    if v.name.is_empty() {
        out.push_str(&v.idx.to_string());
    } else if v.idx == 0 {
        out.push_str(&v.name);
    } else {
        out.push_str(&v.name);
        out.push('.');
        out.push_str(&v.idx.to_string());
    }
}

// =============================================================================
// `show (VTerm Name (BVar LVar))` — used by `checkFormula`'s `exp('g'` probe
// =============================================================================

/// HS `Show (Term a)` applied to `VTerm Name (BVar LVar)`
/// (Term/Raw.hs:219-227 + the derived `Show (BVar v)`).
pub(crate) fn show_gterm(t: &GTerm) -> String {
    let mut s = String::new();
    write_gterm(t, &mut s);
    s
}

fn write_gterm(t: &GTerm, out: &mut String) {
    match t {
        // Lit l -> show l. Var leaves carry a BVar, whose derived Show is
        // `Bound <i>` / `Free <show v>` (LTerm.hs:452-454).
        GTerm::Var(BVar::Bound(i)) => {
            out.push_str("Bound ");
            out.push_str(&i.to_string());
        }
        GTerm::Var(BVar::Free(v)) => {
            out.push_str("Free ");
            write_varspec(v, out);
        }
        // Con (Name PubName n) -> 'n'
        GTerm::PubLit(n) => {
            out.push('\'');
            out.push_str(n);
            out.push('\'');
        }
        // Con (Name FreshName n) -> ~'n'
        GTerm::FreshLit(n) => {
            out.push_str("~'");
            out.push_str(n);
            out.push('\'');
        }
        // Con (Name NatName n) -> %'n'
        GTerm::NatLit(n) => {
            out.push_str("%'");
            out.push_str(n);
            out.push('\'');
        }
        // Numeric / neutral literals render as their irreducible function head.
        // `Number(n)` is an RS-only bare-integer literal with no HS counterpart;
        // render it unquoted, matching the sibling raw-show `show_debruijn_term`
        // (parser wf.rs `show_debruijn_term`: `Number(n) => n.to_string()`).
        GTerm::Number(n) => out.push_str(&n.to_string()),
        // `fAppOne` = `NoEq oneSym` with `oneSymString = "one"` and
        // `fAppNatOne` = `NoEq natOneSym` with `natOneSymString = "tone"`
        // (FunctionSymbols.hs:134-134,144). `show (FApp (NoEq (s,_)) [])` = `s`
        // (Term/Raw.hs:219-230, see line 222), so the two nullary symbols show differently.
        GTerm::NumberOne => out.push_str("one"),
        GTerm::NatOne => out.push_str("tone"),
        GTerm::DhNeutral => out.push_str("DH_neutral"),
        // FApp (NoEq (name,_)) as
        GTerm::App(name, args) => write_app(name, args.iter(), out),
        // `op{a}b` == `op(a,b)` — a NoEq application.
        GTerm::AlgApp(name, a, b) => write_app(name, [a.as_ref(), b.as_ref()], out),
        // `<a,b,c>` is binary-nested `pair(a, pair(b,c))` in HS Term.
        GTerm::Pair(items) => write_pair(items, out),
        // diff is a NoEq symbol named "diff".
        GTerm::Diff(a, b) => {
            out.push_str("diff(");
            write_gterm(a, out);
            out.push(',');
            write_gterm(b, out);
            out.push(')');
        }
        // `^` (exp) is a NoEq symbol named "exp"; the AC ops render with
        // their derived constructor name (Term/Raw.hs:219-230, see line 227 `show o`).
        GTerm::BinOp(op, a, b) => {
            let name = match op {
                p::BinOp::Exp => "exp",
                p::BinOp::Mult => "Mult",
                p::BinOp::Union => "Union",
                p::BinOp::Xor => "Xor",
                p::BinOp::NatPlus => "NatPlus",
            };
            out.push_str(name);
            out.push('(');
            write_gterm(a, out);
            out.push(',');
            write_gterm(b, out);
            out.push(')');
        }
        // Pattern-match wrapper is transparent for `show` purposes.
        GTerm::PatMatch(inner) => write_gterm(inner, out),
    }
}

/// HS `FApp (NoEq (s,_)) as`: `s` if no args, else `s(a1,a2,..)` with no
/// spaces (`intercalate ","`).
fn write_app<'a, I>(name: &str, args: I, out: &mut String)
where
    I: IntoIterator<Item = &'a GTerm>,
{
    out.push_str(name);
    let mut iter = args.into_iter().peekable();
    if iter.peek().is_some() {
        out.push('(');
        let mut first = true;
        for a in iter {
            if !first {
                out.push(',');
            }
            first = false;
            write_gterm(a, out);
        }
        out.push(')');
    }
}

fn write_pair(items: &[GTerm], out: &mut String) {
    // Right-nested binary `pair`: <a,b,c> = pair(a, pair(b, c)).
    match items {
        [] => out.push_str("pair"),
        [single] => write_gterm(single, out),
        [head, rest @ ..] => {
            out.push_str("pair(");
            write_gterm(head, out);
            out.push(',');
            write_pair(rest, out);
            out.push(')');
        }
    }
}

// =============================================================================
// `show (Term (Lit Name LVar))` = `show LNTerm` — used by reasonableNoncesNoise,
// isFactName, isInFactTerms
// =============================================================================

/// HS `Show (Term a)` applied to `LNTerm = VTerm Name LVar` (Term/Raw.hs:219-230).
pub fn show_lnterm(t: &LNTerm) -> String {
    let mut s = String::new();
    write_lnterm(t, &mut s);
    s
}

fn write_lnterm(t: &LNTerm, out: &mut String) {
    use tamarin_term::term::Term;
    match t {
        Term::Lit(Lit::Var(v)) => write_lvar(v, out),
        Term::Lit(Lit::Con(n)) => write_name(n, out),
        Term::App(sym, args) => match sym {
            // FApp (NoEq (s,_)) [] -> s ; FApp (NoEq (s,_)) as -> s(a,..)
            FunSym::NoEq(s) => {
                let name = String::from_utf8_lossy(s.name);
                out.push_str(&name);
                if !args.is_empty() {
                    out.push('(');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push(',');
                        }
                        write_lnterm(a, out);
                    }
                    out.push(')');
                }
            }
            // FApp (C EMap) as -> "em"(..)
            FunSym::C(CSym::EMap) => {
                out.push_str("em(");
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_lnterm(a, out);
                }
                out.push(')');
            }
            // FApp List as -> "LIST"(..)
            FunSym::List => {
                out.push_str("LIST(");
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_lnterm(a, out);
                }
                out.push(')');
            }
            // FApp (AC o) as -> show o (..)  (constructor name)
            FunSym::Ac(o) => {
                let name = match o {
                    AcSym::Union => "Union",
                    AcSym::Mult => "Mult",
                    AcSym::Xor => "Xor",
                    AcSym::NatPlus => "NatPlus",
                };
                out.push_str(name);
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_lnterm(a, out);
                }
                out.push(')');
            }
        },
    }
}

/// HS `show LVar` for the typed `LVar` (LTerm.hs:526-533).  Writes
/// directly into `out`, avoiding a throwaway intermediate `String`;
/// produces byte-identical output.
fn write_lvar(v: &tamarin_term::lterm::LVar, out: &mut String) {
    use tamarin_term::lterm::LSort;
    let prefix = match v.sort {
        LSort::Fresh => "~",
        LSort::Pub => "$",
        LSort::Node => "#",
        LSort::Nat => "%",
        LSort::Msg => "",
    };
    out.push_str(prefix);
    if v.name.is_empty() {
        out.push_str(&v.idx.to_string());
    } else if v.idx == 0 {
        out.push_str(v.name);
    } else {
        out.push_str(v.name);
        out.push('.');
        out.push_str(&v.idx.to_string());
    }
}

/// HS `show Name` (LTerm.hs:231-235).  Writes directly into `out`,
/// avoiding a throwaway intermediate `String`; byte-identical output.
fn write_name(n: &Name, out: &mut String) {
    match n.tag {
        NameTag::Fresh => out.push('~'),
        NameTag::Pub => {}
        NameTag::Node => out.push('#'),
        NameTag::Nat => out.push('%'),
    }
    out.push('\'');
    out.push_str(n.id.0);
    out.push('\'');
}

// =============================================================================
// `show FactTag` (derived Show, Fact.hs:132-143) — used by isFactName
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
                if let GAtom::Action(f, _) = a {
                    out.push(f.name.clone());
                }
            }
            guard_fact_tag_names(body, out);
        }
    }
}

/// HS `getFormulaTerms` (Tactics.hs:203-205): the fact terms of the single
/// top-level guard, when the formula is exactly `GGuarded _ _ [Action _ fa] _`.
fn formula_action_fact(g: &Guarded) -> Option<&GFact> {
    if let Guarded::GGuarded { guards, .. } = g {
        if guards.len() == 1 {
            if let GAtom::Action(fa, _) = &guards[0] {
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
pub(crate) fn check_formula(oracle_type: &str, f: &Guarded) -> Vec<p::VarSpec> {
    // rev = any guard fact-tag name =~ "Reveal"
    let mut tag_names = Vec::new();
    guard_fact_tag_names(f, &mut tag_names);
    let rev = tag_names.iter().any(|n| n.contains("Reveal"));
    if !rev {
        return Vec::new();
    }

    // expG = show (getFormulaTerms f) =~ <pattern>
    // getFormulaTerms returns the top-level Action fact's term args, shown
    // as a Haskell list `[t1,t2,..]`.
    let fact = match formula_action_fact(f) {
        Some(fa) => fa,
        None => return Vec::new(),
    };
    let shown_terms = show_term_list(&fact.args);
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
    let mut acc: Vec<p::VarSpec> = Vec::new();
    for arg in fact.args.iter() {
        let mut vars: Vec<p::VarSpec> = Vec::new();
        crate::guarded_types::collect_free_term(arg, &mut vars);
        // varsVTerm = sortednub (HS Ord LVar = idx, sort, name).
        vars.sort_by(crate::guarded::cmp_varspec);
        vars.dedup_by(|a, b| crate::guarded::cmp_varspec(a, b) == std::cmp::Ordering::Equal);
        acc.extend(vars);
    }
    acc
}

/// HS `show [VTerm Name (BVar LVar)]` — the derived `Show [a]`:
/// `"[" ++ intercalate "," (map show xs) ++ "]"`.
fn show_term_list(args: &[GTerm]) -> String {
    let mut out = String::from("[");
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&show_gterm(a));
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
            out.push(show_varspec(&v));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh(name: &str) -> p::VarSpec {
        p::VarSpec {
            name: name.into(),
            idx: 0,
            sort: p::SortHint::Fresh,
            typ: None,
        }
    }

    #[test]
    fn show_varspec_fresh() {
        assert_eq!(show_varspec(&fresh("s")), "~s");
    }

    #[test]
    fn show_gterm_exp_g() {
        // 'g'^~s  ==>  exp('g',Free ~s)
        let t = GTerm::BinOp(
            p::BinOp::Exp,
            std::sync::Arc::new(GTerm::PubLit("g".into())),
            std::sync::Arc::new(GTerm::Var(BVar::Free(fresh("s")))),
        );
        assert_eq!(show_gterm(&t), "exp('g',Free ~s)");
    }

    #[test]
    fn show_term_list_matches_exp_g() {
        let t = GTerm::BinOp(
            p::BinOp::Exp,
            std::sync::Arc::new(GTerm::PubLit("g".into())),
            std::sync::Arc::new(GTerm::Var(BVar::Free(fresh("s")))),
        );
        let shown = show_term_list(std::slice::from_ref(&t));
        assert_eq!(shown, "[exp('g',Free ~s)]");
    }

    #[test]
    fn show_fact_tag_proto() {
        let t = FactTag::Proto(Multiplicity::Linear, "Foo", 2);
        assert_eq!(show_fact_tag(&t), "ProtoFact Linear \"Foo\" 2");
    }

    #[test]
    fn show_gterm_nat_one_is_tone() {
        // fAppNatOne = FApp (NoEq natOneSym) [] with natOneSymString = "tone"
        // (FunctionSymbols.hs:144-144) => `show fAppNatOne == "tone"`.
        assert_eq!(show_gterm(&GTerm::NatOne), "tone");
    }

    #[test]
    fn show_gterm_number_one_is_one() {
        // fAppOne = FApp (NoEq oneSym) [] with oneSymString = "one"
        // (FunctionSymbols.hs:134-134) => `show fAppOne == "one"`.
        assert_eq!(show_gterm(&GTerm::NumberOne), "one");
    }

    #[test]
    fn show_gterm_number_is_unquoted() {
        // RS-only bare integer literal; raw-show unquoted to match the sibling
        // renderer (parser wf.rs `show_debruijn_term`: `Number(n) => n.to_string()`).
        assert_eq!(show_gterm(&GTerm::Number(5)), "5");
    }
}
