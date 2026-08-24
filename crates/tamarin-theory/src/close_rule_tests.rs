// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::fact::{apply_subst_fact, Fact};
use tamarin_term::subst::apply_vterm;
use tamarin_term::vterm::var_term;

/// KCL07's signature (examples/csf26-ac/fast/KCL07.spthy) plus a Seed
/// rule whose Probe action supplies canonically-elaborated test terms:
/// a user-AC symbol whose destructor group contains a non-subterm rule
/// (`xorr(x, x) = zeroo`) — exactly the family the NDC pass checks.
const XORR_PARENT: &str = "theory NdcStructuralParent\nbegin\n\n\
functions: fst/1, h/1, pair/2, snd/1, xorr/2 [AC], zeroo/0\n\
equations:\n\
    fst(<x.1, x.2>) = x.1,\n\
    snd(<x.1, x.2>) = x.2,\n\
    xorr(xorr(x, y), x) = y,\n\
    xorr(x, x) = zeroo,\n\
    xorr(x, zeroo) = x\n\n\
rule Seed:\n\
  [ Fr( ~k ), In( a ), In( b ), In( c ) ]\n\
  --[ Probe( xorr(a, b), xorr(a, xorr(b, c)), h(<~k, $p, a>), fst(c), zeroo ) ]->\n\
  [ ]\n\n\
end\n";

/// Parse + elaborate [`XORR_PARENT`]; returns the parent `MaudeSig` and the
/// Probe action's five elaborated terms.
fn xorr_parent() -> (tamarin_term::maude_sig::MaudeSig, Vec<LNTerm>) {
    let parsed = tamarin_parser::parse_theory(XORR_PARENT, &[]).expect("parent parses");
    let elab = crate::elaborate::elaborate(&parsed).expect("parent elaborates");
    let rule = elab.rules().next().expect("Seed rule present");
    let probe = rule.rule.actions[0].terms.to_vec();
    assert_eq!(probe.len(), 5, "Probe carries five terms");
    (elab.signature.maude_sig, probe)
}

fn kd(t: LNTerm) -> LNFact {
    Fact::fresh_annotated(FactTag::Kd, Default::default(), vec![t])
}

fn ku(t: LNTerm) -> LNFact {
    Fact::fresh_annotated(FactTag::Ku, Default::default(), vec![t])
}

/// Differential rail: on the SAME (alpha-canonical) inputs, the
/// structural builders and the cfg(test) text pipeline (render →
/// parse → elaborate → guarded) must produce identical values for
/// every field [`prove_deduction_theory`] hands the prover.  The
/// inputs are canonicalised through the text pipeline's own rename
/// first because the rename is internal to that pipeline (the
/// structural path keeps raw variables); on a renamed input the
/// rename is the identity, so names compare byte-for-byte.
///
/// The text side runs under the SYNTHETIC theory's user-fun guard
/// (installed by `elaborate_deduction_theory_via_text`) while the
/// structural side runs under the ambient parent guard, so equality
/// here also exercises the parent-vs-synthetic guard-set equivalence
/// the production path relies on.
fn assert_structural_matches_text(
    sig_text: &str,
    s: &[LNFact],
    fact_term: &LNTerm,
    with_only_once_d: bool,
    label: &str,
) {
    let (s1, t1) = rename_for_render(s, fact_term);
    let (s2, t2) = rename_for_render(&s1, &t1);
    {
        // The rename must have converged (its output re-sorts to the
        // order it assigned), or the byte-comparison below would be
        // comparing differently-named theories.
        let (s3, t3) = rename_for_render(&s2, &t2);
        assert_eq!((&s3, &t3), (&s2, &t2), "{label}: rename converged");
    }
    let (text_rule, text_restrictions, text_lemma) =
        elaborate_deduction_theory_via_text(sig_text, &s2, &t2, with_only_once_d);
    let struct_rule = deduction_rule(&s2);
    let struct_restrictions = deduction_restrictions(with_only_once_d);
    let struct_lemma = deduction_lemma_guarded(&s2, &t2);
    // Whole-struct equality: premises/conclusions/actions, rule info
    // (name + attributes), and `new_vars` — the structural side's HS
    // `[]` (CloseRule.hs:257) must coincide with the text side's
    // parser-recomputed `newVariables` on these inputs (they diverge
    // only for Nat-sorted variables, which `lvarToLnterm` retypes in
    // the premises; keep Nat out of the differential inputs).
    assert_eq!(struct_rule, text_rule, "{label}: Out0 rule");
    assert_eq!(
        struct_restrictions, text_restrictions,
        "{label}: restrictions as guarded"
    );
    assert_eq!(struct_lemma, text_lemma, "{label}: Deduction lemma guarded");
}

/// The differential rail over the representative deduction shapes:
/// user-AC terms (2-ary and flattened 3-ary `xorr`), builtin
/// application + pair + fresh/pub variables, a destructor-headed
/// term, and the zero-data-variable ground case — for both
/// restriction sets (theory-1 with `OnlyOnceD`, theory-2 without).
#[test]
fn structural_deduction_theory_matches_text_pipeline() {
    let (sig, probe) = xorr_parent();
    let sig_text = crate::pretty_theory::render_signature(&sig);
    let (xorr2, xorr3, h_pair, fst_c, zeroo) =
        (&probe[0], &probe[1], &probe[2], &probe[3], &probe[4]);
    let a = var_term(
        tamarin_term::lterm::frees(&vec![xorr2.clone()])
            .into_iter()
            .next()
            .expect("xorr(a, b) has free vars"),
    );
    let cases: Vec<(Vec<LNFact>, &LNTerm, &str)> = vec![
        (
            vec![kd(xorr2.clone()), ku(a.clone())],
            xorr3,
            "user-AC (flat 3-ary xorr under K)",
        ),
        (
            vec![kd(h_pair.clone()), ku(fst_c.clone())],
            h_pair,
            "builtin app + pair + fresh/pub vars + destructor head",
        ),
        (vec![kd(zeroo.clone())], zeroo, "ground, zero data binders"),
    ];
    for (s, fact_term, label) in &cases {
        for ood in [true, false] {
            assert_structural_matches_text(
                &sig_text,
                s,
                fact_term,
                ood,
                &format!("{label}, with_only_once_d={ood}"),
            );
        }
    }
}

/// The structural restriction formulas are exactly what
/// [`crate::formula::from_parser`] builds for the restriction text the
/// render pipeline emits.
#[test]
fn restriction_formulas_equal_their_parsed_text() {
    let src = "theory R\nbegin\n\
restriction OnlyOnce:\n  \"All #ndci #ndcj. OnlyOnce() @ #ndci & OnlyOnce() @ #ndcj ==> #ndci = #ndcj\"\n\
restriction OnlyOnceD:\n  \"All #ndci #ndcj #ndck. OnlyOnceD() @ #ndci & OnlyOnceD() @ #ndcj & OnlyOnceD() @ #ndck ==> #ndci = #ndcj | #ndci = #ndck | #ndcj = #ndck\"\n\
end\n";
    let parsed = tamarin_parser::parse_theory(src, &[]).expect("restriction theory parses");
    // The restriction atoms are nullary facts and timepoint equalities, so
    // no term needs a function symbol from the signature.
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let formulas: Vec<LNFormula> = parsed
        .items
        .iter()
        .filter_map(|it| match it {
            tamarin_parser::ast::TheoryItem::Restriction(r) => Some(&r.formula),
            _ => None,
        })
        .map(|f| {
            let syn = crate::formula::from_parser(f, &sig).expect("restriction closes");
            crate::formula::to_lnformula(&syn).expect("restriction carries no predicate")
        })
        .collect();
    assert_eq!(formulas.len(), 2);
    assert_eq!(formulas[0], only_once_restriction(), "OnlyOnce");
    assert_eq!(formulas[1], only_once_d_restriction(), "OnlyOnceD");
}

/// The guarded values the NDC search runs on, pinned as text: the two
/// restrictions HS `addRestrictions` installs (CloseRule.hs:247,252).  The
/// binder names and their prefix order are the port's, not HS's, and a
/// change to either moves the synthetic search and with it the `[NDC]` tags
/// in the printed `functions:` header.
#[test]
fn only_once_restriction_guarded_is_unchanged() {
    let g = &deduction_restrictions(false)[0];
    assert_eq!(
        crate::pretty_formula::pretty_guarded(g),
        "∀ #ndci #ndcj. (OnlyOnce( ) @ #ndci) ∧ (OnlyOnce( ) @ #ndcj) ⇒ #ndci = #ndcj",
    );
}

/// [`only_once_restriction_guarded_is_unchanged`] for the `OnlyOnceD`
/// restriction, which only theory-1 carries.
#[test]
fn only_once_d_restriction_guarded_is_unchanged() {
    let rs = deduction_restrictions(true);
    assert_eq!(rs.len(), 2, "theory-1 carries both restrictions");
    assert_eq!(
        crate::pretty_formula::pretty_guarded(&rs[1]),
        "∀ #ndci #ndcj #ndck. (OnlyOnceD( ) @ #ndci) ∧ (OnlyOnceD( ) @ #ndcj) ∧ (OnlyOnceD( ) @ #ndck) ⇒ ((#ndci = #ndcj) ∨ (#ndci = #ndck) ∨ (#ndcj = #ndck))",
    );
}

/// [`only_once_restriction_guarded_is_unchanged`] for the `Deduction`
/// lemma, over the shapes the NDC pass meets: dotted unifier indices with a
/// cross-sort Nat variable, a user-AC term, a builtin application with a
/// pair and fresh/public variables, and the ground zero-binder case.
#[test]
fn deduction_lemma_guarded_is_unchanged() {
    let pretty = |s: &[LNFact], t: &LNTerm| {
        crate::pretty_formula::pretty_guarded(&deduction_lemma_guarded(s, t))
    };
    let x0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x5 = var_term(LVar::new("x", LSort::Msg, 5));
    let n = var_term(LVar::new("n", LSort::Nat, 0));
    assert_eq!(
        pretty(
            &[
                kd(tamarin_term::builtin::pair(x0.clone(), x5.clone())),
                ku(n.clone()),
            ],
            &n,
        ),
        "∀ x ~n x.1 %n.1 #ndct0 #ndct1. (Generated_0( x, ~n, x.1 ) @ #ndct0) ∧ (K( %n.1 ) @ #ndct1) ⇒ ⊥",
    );
    let (_sig, probe) = xorr_parent();
    let (xorr2, xorr3, h_pair, fst_c, zeroo) =
        (&probe[0], &probe[1], &probe[2], &probe[3], &probe[4]);
    let a = var_term(
        tamarin_term::lterm::frees(&vec![xorr2.clone()])
            .into_iter()
            .next()
            .expect("xorr(a, b) has free vars"),
    );
    assert_eq!(
        pretty(&[kd(xorr2.clone()), ku(a)], xorr3),
        "∀ a b c #ndct0 #ndct1. (Generated_0( a, b ) @ #ndct0) ∧ (K( (a xorr b xorr c) ) @ #ndct1) ⇒ ⊥",
    );
    assert_eq!(
        pretty(&[kd(h_pair.clone()), ku(fst_c.clone())], h_pair),
        "∀ $p ~k a c #ndct0 #ndct1. (Generated_0( $p, ~k, a, c ) @ #ndct0) ∧ (K( h(<~k, $p, a>) ) @ #ndct1) ⇒ ⊥",
    );
    assert_eq!(
        pretty(&[kd(zeroo.clone())], zeroo),
        "∀ #ndct0 #ndct1. (Generated_0( ) @ #ndct0) ∧ (K( zeroo ) @ #ndct1) ⇒ ⊥",
    );
}

/// HS `landFormula` seeds the lemma conjunction with `ltrue`
/// (CloseRule.hs:200-201: a `foldl` of `.&&.` over `ltrue`), so HS's formula is
/// `(⊤ ∧ Gen@#0) ∧ K@#1` where this module builds `Gen@t0 ∧ K@t1`.
/// `gconj` drops ⊤, making the two shapes convert to the same
/// guarded value — pinned here so the shape difference stays
/// invisible.
#[test]
fn lemma_guarded_is_invariant_to_hs_ltrue_conjunct() {
    let t0 = ndc_node_var("ndct0");
    let t1 = ndc_node_var("ndct1");
    let v = LVar::new("v", LSort::Msg, 0);
    let gen_at: LNFormula = ProtoFormula::Atom(ProtoAtom::Action(
        free_time(&t0),
        crate::fact::proto_fact(Multiplicity::Linear, "Generated_0", vec![var_term(v)])
            .map_ref(lift_free),
    ));
    let k_at: LNFormula = ProtoFormula::Atom(ProtoAtom::Action(
        free_time(&t1),
        crate::fact::k_log_fact(var_term(v)).map_ref(lift_free),
    ));
    let binders = [v, t0, t1];
    let ours = close_ex(&binders, gen_at.clone().and(k_at.clone())).not();
    let hs_shaped = close_ex(&binders, ProtoFormula::ltrue().and(gen_at).and(k_at)).not();
    assert_eq!(
        crate::guarded::formula_to_guarded(&ours).expect("ours converts"),
        crate::guarded::formula_to_guarded(&hs_shaped).expect("HS shape converts"),
    );
}

/// The shapes only the structural path faces — dotted unifier indices
/// (`x.5`) and same-named variables of different sorts (a Nat var:
/// Fresh in the `Generated_0` args via `lvarToLnterm`, Nat inside the
/// K term) — must still produce a CLOSED guarded lemma: every
/// occurrence resolves to its own binder via (name, idx, sort)-keyed
/// matching, mirroring HS's sort-aware `LVar` identity.  (The text
/// pipeline never sees these: its alpha-rename plus the `{name}f`
/// retype-rename in `render_deduction_theory` erase both.)
#[test]
fn structural_lemma_closes_dotted_and_cross_sort_binders() {
    let x0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x5 = var_term(LVar::new("x", LSort::Msg, 5));
    let n = var_term(LVar::new("n", LSort::Nat, 0));
    let s = vec![
        kd(tamarin_term::builtin::pair(x0.clone(), x5.clone())),
        ku(n.clone()),
    ];
    let g = deduction_lemma_guarded(&s, &n);
    assert!(
        crate::guarded::free_vars(&g).is_empty(),
        "every occurrence must resolve to a binder; free vars: {:?}",
        crate::guarded::free_vars(&g)
    );
    match &g {
        Guarded::GGuarded {
            qua: crate::guarded::Quant::All,
            vars,
            guards,
            body,
        } => {
            // Binders: x.0, x.5 (Msg), n:fresh (Generated_0 arg),
            // n:nat (K term), and the two timepoints.
            assert_eq!(vars.len(), 6, "bindings: {:?}", vars);
            assert_eq!(guards.len(), 2, "Generated_0 and K guard atoms");
            assert_eq!(**body, crate::guarded::gfalse());
        }
        other => panic!("negated Ex lemma must convert to GGuarded All, got {other:?}"),
    }
    // The rule side of the same inputs: one Fr premise per free var,
    // HS's literal empty `rNewVars`.
    let rule = deduction_rule(&s);
    assert_eq!(rule.rule.premises.len(), 3);
    assert!(rule.rule.new_vars.is_empty(), "HS newRules passes []");
}

/// End-to-end verdict pin through the structural path: on the KCL07
/// signature the ef3f0468 oracle reports `Function xorr has the NDC
/// property.` on stderr, so `check_close_intr_rule` must tag `xorr`
/// and NDC-mark every xorr destructor rule in the returned cache.
#[test]
fn check_close_intr_rule_tags_xorr_on_kcl07_signature() {
    // The resolution policy lives in [`crate::test_maude::maude_path`]. That
    // policy covers a `MAUDE_PATH` that points nowhere, and it covers a
    // machine with no maude at all. This test calls that one helper so that a
    // private copy of the policy here cannot drift from it.
    let Some(mp) = crate::test_maude::maude_path() else {
        return;
    };
    let (sig, _probe) = xorr_parent();
    let maude = tamarin_term::maude_proc::MaudeHandle::start(&mp, sig)
        .expect("maude starts on the KCL07 signature");
    let checked = check_close_intr_rule(&maude, None, true);
    let names: Vec<String> = checked
        .ndc_funs
        .iter()
        .map(|f| crate::intruder_rules::show_fun_sym_name(f).into_owned())
        .collect();
    assert_eq!(names, vec!["xorr".to_string()]);
    let xorr_destr: Vec<&IntrRuleAC> = checked
        .cache
        .iter()
        .filter(|r| {
            get_destr_rule_function(r)
                .is_some_and(|f| crate::intruder_rules::show_fun_sym_name(&f) == "xorr")
        })
        .collect();
    assert!(
        !xorr_destr.is_empty(),
        "cache carries xorr destructor rules"
    );
    assert!(
        xorr_destr.iter().all(|r| is_ndc_cache_rule(r)),
        "every xorr destructor rule carries the NDC-tagged head"
    );
}

fn pretty_term(t: &LNTerm) -> String {
    tamarin_term::pretty::pretty_lnterm(t)
}

fn pretty_var(v: &LVar) -> String {
    pretty_term(&tamarin_term::vterm::var_term(*v))
}

/// The text pipeline's alpha-rename: every variable of `s` and
/// `fact_term` to a simple idx-0 name (`ndcvN`).  Verdict-invariant, and
/// exists only for parseability — unifier-instantiated rules carry dotted
/// indices (`x.5`), which the `.spthy` grammar cannot express.  The
/// structural builders take the raw variables instead; the tests apply
/// this rename to their inputs so the two pipelines compare byte-equal.
fn rename_for_render(s: &[LNFact], fact_term: &LNTerm) -> (Vec<LNFact>, LNTerm) {
    let mut all_vars: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    for f in s {
        f.for_each_free(&mut |v| {
            all_vars.insert(*v);
        });
    }
    fact_term.for_each_free(&mut |v| {
        all_vars.insert(*v);
    });
    let rename: Vec<(LVar, LNTerm)> = all_vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            (
                *v,
                tamarin_term::vterm::var_term(LVar::new(format!("ndcv{}", i), v.sort, 0)),
            )
        })
        .collect();
    let sigma = tamarin_term::subst::Subst::from_list(rename);
    (
        s.iter().map(|f| apply_subst_fact(&sigma, f)).collect(),
        apply_vterm(&sigma, fact_term.clone()),
    )
}

/// Render the synthetic deduction theory for one decomposition `s`
/// (HS `modifiedTheory1/2`): the parent signature `sig_text`, the `Out0`
/// source rule, the `OnlyOnce` (and optionally `OnlyOnceD`) restrictions,
/// and the `Deduction` lemma, as `.spthy` text via the parity-grade
/// printers.  Test-only: the production path builds the same theory
/// structurally ([`prove_deduction_theory`]); this renderer plus
/// [`elaborate_deduction_theory_via_text`] are the differential reference
/// the tests hold the structural builders against.
fn render_deduction_theory(
    sig_text: &str,
    s: &[LNFact],
    fact_term: &LNTerm,
    with_only_once_d: bool,
) -> String {
    let (s, fact_term) = rename_for_render(s, fact_term);

    // varD s (HS: `frees $ concatMap factTerms s` — `sortednub . freesList`;
    // the ordering fixes the `Generated_0` argument order, used consistently
    // on the rule and lemma sides).
    let var_d: Vec<LVar> = tamarin_term::lterm::frees(&s);

    // Rule premises: `freesToFresh . varFresh` — Fr(lvarToLnterm
    // (msgToFreshVars v)).
    let prems: Vec<LNFact> = var_d
        .iter()
        .map(|v| crate::fact::fresh_fact(crate::fact::lvar_to_lnterm(&msg_to_fresh_var(v))))
        .collect();
    // Conclusions: `map (outFact . msgToFreshTerms) (concatMap factTerms s)`.
    let concs: Vec<LNFact> = s
        .iter()
        .flat_map(|f| f.terms.iter())
        .map(|t| crate::fact::out_fact(msg_to_fresh_terms(t)))
        .collect();
    // Actions: Generated_0 over the retyped vars, plus OnlyOnce.
    let gen_args_rule: Vec<LNTerm> = var_d
        .iter()
        .map(|v| msg_to_fresh_terms(&crate::fact::lvar_to_lnterm(v)))
        .collect();
    let act_gen = crate::fact::proto_fact(Multiplicity::Linear, "Generated_0", gen_args_rule);
    let act_oo = crate::fact::proto_fact(Multiplicity::Linear, "OnlyOnce", vec![]);

    // Lemma-side Generated_0 args: `map lvarToLnterm (varD s)` — NO
    // msg→fresh retype.  A nat→fresh retype changes the variable's sort
    // relative to any occurrence inside the K term; give the retyped var
    // a distinct name so the two remain independent binders under the
    // name-keyed guarded conversion (HS distinguishes them by sort-aware
    // LVar identity).
    let gen_args_lemma: Vec<LNTerm> = var_d
        .iter()
        .map(|v| {
            let vt = crate::fact::lvar_to_lnterm(v);
            match &vt {
                Term::Lit(tamarin_term::vterm::Lit::Var(nv)) if nv.sort != v.sort => {
                    tamarin_term::vterm::var_term(LVar::new(
                        format!("{}f", nv.name),
                        nv.sort,
                        nv.idx,
                    ))
                }
                _ => vt,
            }
        })
        .collect();

    let pf = crate::pretty_system::pretty_fact;
    let mut out = String::new();
    out.push_str("theory checkDeduction\nbegin\n\n");
    out.push_str(sig_text);
    out.push('\n');
    out.push_str(&format!(
        "rule Out0:\n  [ {} ]\n  --[ {}, {} ]->\n  [ {} ]\n\n",
        prems.iter().map(pf).collect::<Vec<_>>().join(", "),
        pf(&act_gen),
        pf(&act_oo),
        concs.iter().map(pf).collect::<Vec<_>>().join(", "),
    ));
    out.push_str(
        "restriction OnlyOnce:\n  \"All #ndci #ndcj. OnlyOnce() @ #ndci & OnlyOnce() @ #ndcj ==> #ndci = #ndcj\"\n\n",
    );
    if with_only_once_d {
        out.push_str(
            "restriction OnlyOnceD:\n  \"All #ndci #ndcj #ndck. OnlyOnceD() @ #ndci & OnlyOnceD() @ #ndcj & OnlyOnceD() @ #ndck ==> #ndci = #ndcj | #ndci = #ndck | #ndcj = #ndck\"\n\n",
        );
    }
    // Lemma: Not(Ex vars #t0 #t1. Generated_0(..) @ #t0 & K(t) @ #t1).
    let mut binder_vars: Vec<String> = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for t in gen_args_lemma.iter().chain(std::iter::once(&fact_term)) {
        t.for_each_free(&mut |v: &LVar| {
            let r = pretty_var(v);
            if seen.insert(r.clone()) {
                binder_vars.push(r);
            }
        });
    }
    let gen_args_str: Vec<String> = gen_args_lemma.iter().map(pretty_term).collect();
    // Data-var binder prefix: each var followed by exactly one space, so
    // the quantifier list reads `Ex v0 v1 #ndct0 #ndct1.` (and just
    // `Ex #ndct0 #ndct1.` with zero data vars).
    let binder_prefix = if binder_vars.is_empty() {
        String::new()
    } else {
        format!("{} ", binder_vars.join(" "))
    };
    out.push_str(&format!(
        "lemma Deduction:\n  all-traces\n  \"not(Ex {}#ndct0 #ndct1. Generated_0({}) @ #ndct0 & K({}) @ #ndct1)\"\n\nend\n",
        binder_prefix,
        gen_args_str.join(", "),
        pretty_term(&fact_term),
    ));
    out
}

/// Head and tail of a rendered deduction theory, for panic context: the
/// header/signature and the `Out0` rule plus `Deduction` lemma, without
/// dumping a signature of arbitrary size.
fn theory_snippet(src: &str) -> String {
    const HEAD: usize = 300;
    const TAIL: usize = 300;
    let n = src.chars().count();
    if n <= HEAD + TAIL {
        return src.to_string();
    }
    let head: String = src.chars().take(HEAD).collect();
    let tail: String = src.chars().skip(n - TAIL).collect();
    format!("{}\n...\n{}", head, tail)
}

/// The text pipeline's elaborated forms for one synthetic deduction
/// theory: render ([`render_deduction_theory`]), parse, elaborate, and
/// project exactly the fields [`prove_deduction_theory`] hands the
/// prover — the `Out0` rule, the restrictions as guarded formulas, and
/// the `Deduction` lemma's guarded formula.  Differential reference for
/// the structural builders; any failure panics with the rendered theory
/// attached.
fn elaborate_deduction_theory_via_text(
    sig_text: &str,
    s: &[LNFact],
    fact_term: &LNTerm,
    with_only_once_d: bool,
) -> (crate::theory::OpenProtoRule, Vec<Guarded>, Guarded) {
    let src = render_deduction_theory(sig_text, s, fact_term, with_only_once_d);
    let parsed = tamarin_parser::parse_theory(&src, &[]).unwrap_or_else(|e| {
        panic!(
            "[ndc] synthetic deduction theory failed to parse ({}); theory:\n{}",
            e,
            theory_snippet(&src)
        )
    });
    let elaborated = crate::elaborate::elaborate(&parsed).unwrap_or_else(|e| {
        panic!(
            "[ndc] synthetic deduction theory failed to elaborate ({}); theory:\n{}",
            e.message,
            theory_snippet(&src)
        )
    });
    let mut rules: Vec<crate::theory::OpenProtoRule> = elaborated.rules().cloned().collect();
    assert_eq!(
        rules.len(),
        1,
        "synthetic deduction theory carries exactly the Out0 rule"
    );
    let msig = &elaborated.signature.maude_sig;
    let restrictions: Vec<Guarded> = elaborated
        .restrictions()
        .map(|r| {
            crate::guarded::formula_to_guarded(&r.formula).unwrap_or_else(|e| {
                panic!(
                    "[ndc] synthetic deduction theory restriction {} is not guarded ({}); theory:\n{}",
                    r.name,
                    e.message,
                    theory_snippet(&src)
                )
            })
        })
        .collect();
    let lemma = elaborated.lookup_lemma("Deduction").unwrap_or_else(|| {
        panic!(
            "[ndc] synthetic deduction theory has no Deduction lemma; theory:\n{}",
            theory_snippet(&src)
        )
    });
    let g = crate::guarded::formula_to_guarded_parsed(&lemma.formula, msig).unwrap_or_else(|e| {
        panic!(
            "[ndc] synthetic deduction theory Deduction lemma is not guarded ({}); theory:\n{}",
            e.message,
            theory_snippet(&src)
        )
    });
    (rules.remove(0), restrictions, g)
}
