// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::sapic::ProcessParsedAnnotation;
use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
use tamarin_term::lterm::{LSort, LVar};
use tamarin_term::term::f_app_no_eq;
use tamarin_term::vterm::VTerm;

fn sv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
    SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(String::from))
}

#[test]
fn new_top_level() {
    let p = Process::Action(
        SapicAction::New(sv("x", 1, Some("lol"))),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    assert_eq!(pretty_sapic_top_level(&p), "new x.1:lol;");
}

#[test]
fn out_ffx_top_level() {
    let f = NoEqSym::new(
        b"f".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let x = VTerm::Lit(Lit::Var(sv("x", 1, Some("lol"))));
    let ffx = f_app_no_eq(f, vec![f_app_no_eq(f, vec![x])]);
    let p = Process::Action(
        SapicAction::ChOut {
            chan: None,
            msg: ffx,
        },
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    assert_eq!(pretty_sapic_top_level(&p), "out(f(f(x.1:lol)));");
}

#[test]
fn event_top_level_has_spaces() {
    let x = VTerm::Lit(Lit::Var(sv("x", 1, Some("lol"))));
    let fact = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Test", 1),
        vec![x],
    );
    let p = Process::Action(
        SapicAction::Event(fact),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    assert_eq!(pretty_sapic_top_level(&p), "event Test( x.1:lol );");
}

#[test]
fn user_ac_term_infix_and_nullary() {
    use tamarin_term::function_symbols::{AcFctSym, AcSym, NdcState};
    let f = AcFctSym::new(
        b"f".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let x = VTerm::Lit(Lit::Var(sv("x", 1, None)));
    let y = VTerm::Lit(Lit::Var(sv("y", 1, None)));
    let applied = tamarin_term::term::f_app_ac(AcSym::AcFct(f), vec![x, y]);
    assert_eq!(pretty_sapic_term(&applied), "(x.1 f y.1)");
    // HS `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term/Term.hs:304):
    // the bare name, no parens.  `f_app_ac` rejects an empty argument list
    // (HS `fAppAC` errors likewise, Raw.hs:120), so no theory text reaches
    // this arm — it is here to keep the printer the shape of `prettyTerm`.
    let nullary: SapicTerm = VTerm::App(FunSym::Ac(AcSym::AcFct(f)), vec![].into());
    assert_eq!(pretty_sapic_term(&nullary), "f");
}

#[test]
fn null_top_level() {
    let p: PlainProcess = Process::Null(ProcessParsedAnnotation::empty());
    assert_eq!(pretty_sapic_top_level(&p), "0");
}

/// The Maude signature of a one-line theory, for building a condition
/// from source text the way the SAPIC parser does.
fn sig_of(decl: &str) -> tamarin_term::maude_sig::MaudeSig {
    let thy = tamarin_parser::parse_theory(&format!("theory T begin\n{decl}\nend"), &[]).unwrap();
    crate::elaborate::elaborate(&thy).unwrap().signature
}

/// `if <formula>` as the process printer renders it, with `formula` read
/// against the signature `decl` declares.
fn cond_render(src: &str, decl: &str) -> String {
    let sig = sig_of(decl);
    let f = tamarin_parser::parser::parse_formula_str(src, &sig).unwrap();
    let proc: PlainProcess = Process::Comb(
        ProcessCombinator::Cond(crate::formula::sapic_from_parser(&f, &sig).unwrap()),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    pretty_sapic_top_level(&proc)
}

/// A conditional renders its formula STANDALONE, so a conjunction wider
/// than the HughesPJ default page breaks and the second conjunct starts a
/// new line at column 0.
///
/// Oracle bytes (pinned build, Git revision ef3f0468) for
/// `functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1` +
/// `predicates: Longer(xxxxxxxxxx, yyyyyyyyyy) <=> xxxxxxxxxx = yyyyyyyyyy` +
/// `in(<xxxxxxxxxx, yyyyyyyyyy, zzzzzzzzzz>); if Longer(aaaaaaaaaa(xxxxxxxxxx), bbbbbbbbbb(yyyyyyyyyy)) & Longer(cccccccccc(zzzzzzzzzz), aaaaaaaaaa(yyyyyyyyyy)) then …`
/// (fixture `sapic_cond_wrap`).
#[test]
fn cond_wraps_at_the_hughespj_default_width() {
    let got = cond_render(
        "Longer(aaaaaaaaaa(xxxxxxxxxx.1), bbbbbbbbbb(yyyyyyyyyy.1)) \
             & Longer(cccccccccc(zzzzzzzzzz.1), aaaaaaaaaa(yyyyyyyyyy.1))",
        "functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1",
    );
    assert_eq!(
        got,
        "if (Longer( aaaaaaaaaa(xxxxxxxxxx.1), bbbbbbbbbb(yyyyyyyyyy.1) )) ∧\n\
             (Longer( cccccccccc(zzzzzzzzzz.1), aaaaaaaaaa(yyyyyyyyyy.1) ))"
    );
    // The derived rule name is `filter isAlpha` over the same string
    // (Sapic/Facts.hs:401#stripNonAlphanumerical), so the break leaves it
    // untouched.
    let name: String = got.chars().filter(|c| c.is_alphabetic()).collect();
    assert_eq!(
        name,
        "ifLongeraaaaaaaaaaxxxxxxxxxxbbbbbbbbbbyyyyyyyyyyLongercccccccccczzzzzzzzzzaaaaaaaaaayyyyyyyyyy"
    );
}

/// `if <formula>` renders its user-`[AC]` applications the way HS's
/// signature-built `SapicTerm`s do: flattened, sorted, infix.
///
/// Oracle bytes (pinned build, Git revision ef3f0468) for
/// `functions: add/2 [AC]` + `predicates: Eq(a, b) <=> a = b` +
/// `in(k); if Eq(<'g'^k, add(k,'a')>, k) then out('yes') else out('no')`:
///   `process="if Eq( <'g'^k.1, ('a' add k.1)>, k.1 )"`
/// and for `if Eq(add(k, add('a','b')), k)`:
///   `process="if Eq( ('a' add 'b' add k.1), k.1 )"`.
#[test]
fn cond_renders_user_ac_flattened_sorted_and_infix() {
    // `^` is a term operator only under `builtins: diffie-hellman`
    // (Theory/Text/Parser/Term.hs:179-185).
    // With `add` an ordinary function symbol the application stays
    // prefix, which is what makes the AC assertions below discriminating.
    assert_eq!(
        cond_render(
            "Eq(<'g'^k.1, add(k.1,'a')>, k.1)",
            "builtins: diffie-hellman\nfunctions: add/2"
        ),
        "if Eq( <'g'^k.1, add(k.1, 'a')>, k.1 )"
    );
    assert_eq!(
        cond_render(
            "Eq(<'g'^k.1, add(k.1,'a')>, k.1)",
            "builtins: diffie-hellman\nfunctions: add/2 [AC]"
        ),
        "if Eq( <'g'^k.1, ('a' add k.1)>, k.1 )"
    );
    // A nested chain flattens to three operands under one AC node.
    assert_eq!(
        cond_render("Eq(add(k.1, add('a','b')), k.1)", "functions: add/2 [AC]"),
        "if Eq( ('a' add 'b' add k.1), k.1 )"
    );
}

/// An embedded MSR as the process printer renders it: one `Ev(<arg>)`
/// action and one `_restrict(<restr>)`, both read against the signature
/// `decl` declares.
fn msr_render(arg: &str, restr: &str, decl: &str) -> String {
    use tamarin_parser::ast::{Atom, Formula};

    let sig = sig_of(decl);
    // The action's argument comes back out of an action atom, the formula
    // entry point's way of reading one term with `sig`'s symbols.
    let action =
        tamarin_parser::parser::parse_formula_str(&format!("Ev({arg}) @ #i"), &sig).unwrap();
    let t = match &action {
        Formula::Atom(Atom::Action(fact, _)) => fact.args[0].clone(),
        other => panic!("expected an action atom, got {other:?}"),
    };
    let f = tamarin_parser::parser::parse_formula_str(restr, &sig).unwrap();
    let ev = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Ev", 1),
        vec![crate::elaborate::term_to_sapic_term(&t, &sig).unwrap()],
    );
    let proc: PlainProcess = Process::Action(
        SapicAction::Msr {
            prems: Vec::new(),
            acts: vec![ev],
            concs: Vec::new(),
            rest: vec![crate::formula::sapic_from_parser(&f, &sig).unwrap()],
            match_vars: std::collections::BTreeSet::new(),
        },
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    pretty_sapic_top_level(&proc)
}

/// An MSR's embedded `_restrict(...)` renders its user-`[AC]` applications
/// the way HS's signature-built `SapicTerm`s do: flattened, sorted, infix.
/// The render feeds both the `process="..."` attribute and the
/// SAPIC-derived rule/restriction names.
///
/// Oracle bytes (pinned build, Git revision ef3f0468) for
/// `in(k); [ ] --[ Ev(add(k,'a')), _restrict(add(k,'a') = k) ]-> [ ]; out('y')`
/// with `functions: add/2 [AC]`:
///   `process=" [ ] --[ Ev( ('a' add k.1) ), _restrict(('a' add k.1) = k.1) ]-> [ ];"`
/// and with `functions: add/2`:
///   `process=" [ ] --[ Ev( add(k.1, 'a') ), _restrict(add(k.1, 'a') = k.1) ]-> [ ];"`
#[test]
fn msr_restriction_renders_user_ac_flattened_sorted_and_infix() {
    // With `add` an ordinary function symbol the application stays
    // prefix, which is what makes the AC assertion below discriminating.
    assert_eq!(
        msr_render("add(k.1,'a')", "add(k.1,'a') = k.1", "functions: add/2"),
        " [ ] --[ Ev( add(k.1, 'a') ), _restrict(add(k.1, 'a') = k.1) ]-> [ ];"
    );
    assert_eq!(
        msr_render(
            "add(k.1,'a')",
            "add(k.1,'a') = k.1",
            "functions: add/2 [AC]"
        ),
        " [ ] --[ Ev( ('a' add k.1) ), _restrict(('a' add k.1) = k.1) ]-> [ ];"
    );
}

/// `prettyFact`'s annotation suffix (Theory/Model/Fact.hs:573-574) reaches
/// the embedded MSR through `rulePrinter`'s `ppFact = prettyFact $
/// prettyTerm $ text . show` (Print.hs:43), so an annotated fact carries
/// its `[…]` into the `process="…"` attribute — and, through
/// `filter isAlpha` (Sapic/Facts.hs:401#stripNonAlphanumerical), into the
/// derived rule name.
///
/// Oracle bytes (pinned build, Git revision ef3f0468) for
/// `in('c', x); [ St(x)[+] ] --[ Ev(x)[no_precomp] ]-> [ Out(x) ]`:
///   `rule (modulo E) StxEvxnoprecompOutx_0_1[…, process=" [ St( x.2 )[+] ] --[ Ev( x.2 )[no_precomp] ]-> [ Out( x.2 ) ];", …]`
#[test]
fn msr_facts_carry_their_annotations() {
    use crate::fact::{Fact, FactAnnotation, FactTag, Multiplicity};

    let x: SapicTerm = VTerm::Lit(Lit::Var(sv("x", 2, None)));
    let annotated = |name: &'static str, a: FactAnnotation| {
        Fact::new(
            FactTag::Proto(Multiplicity::Linear, name, 1),
            vec![x.clone()],
        )
        .annotate(a)
    };
    let proc: PlainProcess = Process::Action(
        SapicAction::Msr {
            prems: vec![annotated("St", FactAnnotation::SolveFirst)],
            acts: vec![annotated("Ev", FactAnnotation::NoSources)],
            concs: vec![Fact::new(FactTag::Out, vec![x])],
            rest: Vec::new(),
            match_vars: std::collections::BTreeSet::new(),
        },
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    let got = pretty_sapic_top_level(&proc);
    assert_eq!(
        got,
        " [ St( x.2 )[+] ] --[ Ev( x.2 )[no_precomp] ]-> [ Out( x.2 ) ];"
    );
    let name: String = got.chars().filter(|c| c.is_alphabetic()).collect();
    assert_eq!(name, "StxEvxnoprecompOutx");
}

/// The restriction item is the Doc composition `_restrict(` <> formula <>
/// `)`, so a break the formula takes indents by the ten columns of the
/// opening operator and the whole item lays out inside the rule.
///
/// Oracle bytes (pinned build, Git revision ef3f0468) for
/// `functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1` +
/// `in(<xxxxxxxxxx, yyyyyyyyyy, zzzzzzzzzz>); [ ] --[ Ev(xxxxxxxxxx), _restrict( aaaaaaaaaa(xxxxxxxxxx) = bbbbbbbbbb(yyyyyyyyyy) & cccccccccc(zzzzzzzzzz) = aaaaaaaaaa(yyyyyyyyyy) ) ]-> [ ]; out('a')`
/// (fixture `sapic_msr_restrict_wrap`).
#[test]
fn msr_restrict_wraps_under_the_restrict_paren() {
    let got = msr_render(
        "xxxxxxxxxx.1",
        "aaaaaaaaaa(xxxxxxxxxx.1) = bbbbbbbbbb(yyyyyyyyyy.1) \
             & cccccccccc(zzzzzzzzzz.1) = aaaaaaaaaa(yyyyyyyyyy.1)",
        "functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1",
    );
    assert_eq!(
        got,
        " [ ]\n\
             --[\n\
             Ev( xxxxxxxxxx.1 ),\n\
             _restrict((aaaaaaaaaa(xxxxxxxxxx.1) = bbbbbbbbbb(yyyyyyyyyy.1)) \u{2227}\n\
             \x20         (cccccccccc(zzzzzzzzzz.1) = aaaaaaaaaa(yyyyyyyyyy.1)))\n\
             ]->\n\
             \x20[ ];"
    );
    // The derived rule name is `filter isAlpha` over the same string
    // (Sapic/Facts.hs:401#stripNonAlphanumerical), so the breaks leave it
    // untouched.
    let name: String = got.chars().filter(|c| c.is_alphabetic()).collect();
    assert_eq!(
        name,
        "Evxxxxxxxxxxrestrictaaaaaaaaaaxxxxxxxxxxbbbbbbbbbbyyyyyyyyyycccccccccczzzzzzzzzzaaaaaaaaaayyyyyyyyyy"
    );
}

/// The `process="..."` rule attribute and the `process:` block are plain
/// text inside the page's `Doc`: an interactive-server page render holds
/// an [`hpj::HtmlDocGuard`], and the process text must still reach that
/// `Doc` unescaped and measured at its visible width, so the page escapes
/// each metacharacter exactly once.
#[test]
fn top_level_attr_is_plain_text_under_html_mode() {
    use tamarin_term::function_symbols::pair_sym;
    use tamarin_term::lterm::{Name, NameTag};
    let msg = f_app_no_eq(
        pair_sym(),
        vec![
            VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "p"))),
            VTerm::Lit(Lit::Var(sv("x", 1, None))),
        ],
    );
    let p: PlainProcess = Process::Action(
        SapicAction::ChOut { chan: None, msg },
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    let _html = hpj::HtmlDocGuard::enable();
    let attr = pretty_sapic_top_level_attr(&p);
    assert_eq!(attr, "out(<'p', x.1>);");
    assert_eq!(
        Doc::text(format!("process=\"{attr}\"")).render_with(200, 200),
        "process=&quot;out(&lt;&#39;p&#39;, x.1&gt;);&quot;"
    );
}
