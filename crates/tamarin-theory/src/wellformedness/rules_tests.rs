// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::super::check_theory;
use super::*;
use crate::sapic::{ProcessParsedAnnotation, SapicLVar};
use crate::theory::TheoryItem;
use tamarin_term::vterm::var_term;

/// The elaborated theory for `src`, as a loader holds it before
/// translation.
fn elaborated(src: &str) -> Theory {
    let parsed = tamarin_parser::parse_theory(src, &[]).expect("parse");
    crate::elaborate::elaborate(&parsed).expect("elaborate")
}

/// The report's bodies joined the way `prettyWfErrorReport` joins a topic
/// group — `intersperse (text "")` under one header, which at the group's
/// 2-space nest is a two-space line (Wellformedness.hs:118-125).
fn bodies(report: &[WfError]) -> String {
    assert!(!report.is_empty(), "empty report");
    report
        .iter()
        .map(|e| e.message.clone())
        .collect::<Vec<_>>()
        .join("\n  \n")
}

/// A `lookup t as v` combinator over one variable, as the `process`
/// attribute of a SAPIC-generated rule carries it.
fn lookup_process(v: LVar) -> crate::sapic::PlainProcess {
    let sv = SapicLVar::untyped(v);
    Process::Comb(
        ProcessCombinator::Lookup(var_term(sv.clone()), sv),
        ProcessParsedAnnotation::default(),
        Box::new(Process::Null(ProcessParsedAnnotation::default())),
        Box::new(Process::Null(ProcessParsedAnnotation::default())),
    )
}

/// HS `frees` sorts by `Ord LVar` = `(idx, sort, name)`
/// (LTerm.hs:546-548), so the list is not in source order: `~nr` (fresh)
/// precedes the msg-sorted `mi` and `ni`, and `$A` is dropped as
/// pub-sorted.  Byte-pinned to the pinned oracle (ef3f0468) on
/// `Out(<ni, ~nr, $A, mi>)`.
#[test]
fn unbound_variables_are_listed_in_lvar_order() {
    let thy = elaborated("theory T begin rule R: [ ] --[ ]-> [ Out(<ni, ~nr, $A, mi>) ] end");
    assert_eq!(
        bodies(&unbound_report(&thy)),
        "  rule `R' has unbound variables: \n    ~nr, mi, ni"
    );
}

/// A builtin's 0-arity constant is a symbol only while that builtin is
/// enabled (`nullaryApp`, Theory/Text/Parser/Term.hs:158-163), so the same
/// bare name is a variable — and an unbound one — in a theory that does
/// not enable it.
#[test]
fn bare_name_of_a_disabled_builtin_constant_is_a_variable() {
    let thy = elaborated("theory T begin rule R: [ ] --[ ]-> [ Out(<zero, true>) ] end");
    assert_eq!(
        bodies(&unbound_report(&thy)),
        "  rule `R' has unbound variables: \n    true, zero"
    );
    let thy = elaborated(
        "theory T begin builtins: xor, signing rule R: [ ] --[ ]-> [ Out(<zero, true>) ] end",
    );
    assert!(
        unbound_report(&thy).is_empty(),
        "with the builtins enabled both names are constants: {:?}",
        unbound_report(&thy)
    );
}

/// HS `originatesFromLookup` (Wellformedness.hs:501-503, 506-510): the
/// variable a `lookup t as v` combinator binds reaches its generated rule
/// through the `IsIn( t, v )` action, so it is not unbound — while an
/// otherwise identical rule without the `process` attribute is.  The
/// parser never mints that attribute, so the generated shape is built by
/// attaching the process the SAPIC translation writes.
#[test]
fn lookup_binder_is_not_unbound() {
    let src = "theory T begin \
               rule L: [ State_1(m.1) ] --[ IsIn(m.1, v.1) ]-> [ State_11(m.1, v.1) ] \
               end";
    let mut thy = elaborated(src);
    assert_eq!(
        unbound_report(&thy).len(),
        1,
        "without the lookup attribute v.1 is unbound"
    );
    let binder = LVar::new("v", LSort::Msg, 1);
    for item in thy.items.iter_mut() {
        if let TheoryItem::Rule(r) = item {
            r.rule.info.attributes.process = Some(lookup_process(binder));
        }
    }
    assert!(
        unbound_report(&thy).is_empty(),
        "the lookup binder must be suppressed: {:?}",
        unbound_report(&thy)
    );

    // A DIFFERENT free variable in the same lookup rule is still
    // reported: HS compares the offender against the binder, it does not
    // exempt the whole rule.
    let mut thy = elaborated(
        "theory T begin \
         rule L: [ State_1(m.1) ] --[ IsIn(m.1, v.1) ]-> [ State_11(m.1, v.1, w.2) ] \
         end",
    );
    for item in thy.items.iter_mut() {
        if let TheoryItem::Rule(r) = item {
            r.rule.info.attributes.process = Some(lookup_process(binder));
        }
    }
    let report = unbound_report(&thy);
    assert_eq!(report.len(), 1);
    assert_eq!(
        report[0].message, "  rule `L' has unbound variables: \n    w.2",
        "only the non-binder variable is reported: {report:?}"
    );
}

/// The only operand the check rejects is the fresh variable `~x`; the
/// nat-sorted `%a` passes `isNatVar`.  The message carries no rule name
/// and `t` is the complete fact-argument term, whose `%+` operands print
/// in `Ord LVar` order rather than source order — `fAppAC` sorts them at
/// construction.  Byte-pinned to the pinned oracle (ef3f0468) on
/// `Out(%a %+ ~x)`.
#[test]
fn nat_sorts_message_format() {
    let thy = elaborated(
        "theory T begin builtins: natural-numbers \
         rule R: [ Fr(~x) ] --[ ]-> [ Out(%a %+ ~x) ] end",
    );
    assert_eq!(
        bodies(&nat_well_sorted_report(&thy)),
        "  ~x in term (~x%+%a) must be of sort nat"
    );
}

/// The check flags a nat *literal* `%'a'`, which is a `Con` name and not
/// a variable, and leaves the nat variable `%y` beside it — HS `isNatVar`
/// is true only for a `Lit (Var ..)` of sort nat.  Byte-pinned to the
/// pinned oracle (ef3f0468).
#[test]
fn nat_sorts_flags_nat_literal() {
    let thy = elaborated(
        "theory T begin builtins: natural-numbers \
         rule R: [ Fr(~x) ] --[ ]-> [ Out(%'a' %+ %y) ] end",
    );
    assert_eq!(
        bodies(&nat_well_sorted_report(&thy)),
        "  %'a' in term (%'a'%+%y) must be of sort nat"
    );
}

/// Both the offender and the enclosing term print through `prettyLNTerm`
/// over the canonical term, and `nonWellSorted` walks the canonical
/// operand list, so an AC chain appears flattened and sorted and several
/// offenders of one term arrive in that same order.  Byte-pinned to the
/// pinned oracle (ef3f0468).
#[test]
fn nat_sorts_render_ac_terms_canonically() {
    let report = |src: &str| -> String {
        let thy = elaborated(&format!(
            "theory T begin \
             builtins: multiset, xor, bilinear-pairing, natural-numbers \
             functions: add/2 [AC], zz/1 \
             rule R: [ In(<a,b,c>) ] --> [ Out( {src} ) ] end"
        ));
        bodies(&nat_well_sorted_report(&thy))
    };
    assert_eq!(
        report("(a*b)*c %+ %1"),
        "  (a*b*c) in term (%1%+(a*b*c)) must be of sort nat"
    );
    assert_eq!(
        report("add(add(b,a),c) %+ %1"),
        "  (a add b add c) in term (%1%+(a add b add c)) must be of sort nat"
    );
    assert_eq!(
        report("em(b,a) %+ %1"),
        "  em(a, b) in term (%1%+em(a, b)) must be of sort nat"
    );
    assert_eq!(
        report("zz(b*a) %+ %1"),
        "  zz((a*b)) in term (%1%+zz((a*b))) must be of sort nat"
    );
    // `fAppAC _ [a] = a`: the offender is `a`, not `add(a)`.
    assert_eq!(
        report("add(a) %+ %1"),
        "  a in term (a%+%1) must be of sort nat"
    );
    // `exp` is `NoEq`, so it renders unparenthesised.
    assert_eq!(
        report("(a^b) %+ %1"),
        "  a^b in term (a^b%+%1) must be of sort nat"
    );
    // Two offenders under one `%+`, in canonical operand order (the LIT
    // `c` before the `Mult`-headed FAPP) rather than source order.
    assert_eq!(
        report("(a*b) %+ c %+ %1"),
        "  c in term (c%+%1%+(a*b)) must be of sort nat\n  \n  \
         (a*b) in term (c%+%1%+(a*b)) must be of sort nat"
    );
}

/// One entry per `(term, offending operand)` pair, so a `%+` with two
/// rejected operands opens two bodies under the one topic header.
/// Byte-pinned to the pinned oracle (ef3f0468) on `In( x %+ pair(a,b) )`.
#[test]
fn nat_sorts_reports_every_offending_operand_of_a_term() {
    let thy = elaborated(
        "theory T begin builtins: natural-numbers \
         rule Test: [ In( x %+ pair(a,b) ) ] --[ ]-> [] end",
    );
    assert_eq!(
        bodies(&nat_well_sorted_report(&thy)),
        "  x in term (x%+<a, b>) must be of sort nat\n  \n  \
         <a, b> in term (x%+<a, b>) must be of sort nat"
    );
}

/// A free variable literally named `True` is unbound: there is no builtin
/// `True` nullary (only `true`), so the parser leaves it a variable.
#[test]
fn variable_named_true_is_unbound() {
    let thy = elaborated("theory T begin rule R: [ ] --[ ]-> [ Out(True) ] end");
    assert_eq!(
        bodies(&unbound_report(&thy)),
        "  rule `R' has unbound variables: \n    True"
    );
}

/// `prettyVarList` is HS's `fsep` paragraph fill, so the variable cells
/// break before the one that would pass the ribbon — 4-column cells:
/// thirteen fit at 64, fourteen would need 69.  Byte-pinned to the pinned
/// oracle (ef3f0468).
#[test]
fn unbound_variable_list_fills_at_the_report_ribbon() {
    let names: Vec<String> = (1..=20).map(|i| format!("K( a{i:02} )")).collect();
    let thy = elaborated(&format!(
        "theory T begin rule R: [] --[ {} ]-> [] end",
        names.join(", ")
    ));
    assert_eq!(
        bodies(&unbound_report(&thy)),
        "  rule `R' has unbound variables: \n    \
         a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13,\n    \
         a14, a15, a16, a17, a18, a19, a20"
    );
}

/// The parser inlines a rule's `let` bindings into the body it builds
/// (`apply subst (ps0,as0,cs0,rs0)`, Theory/Text/Parser/Rule.hs:119), so
/// the check reads the substituted facts: `c %+ %1` is nat well sorted
/// once `c` is the nat variable `%i`.
#[test]
fn let_inlining_reaches_the_nat_check() {
    let thy = elaborated(
        "theory T begin builtins: natural-numbers \
         rule Count: let c = %i in [In(<'c', %i>)] --[Count(c %+ %1)]-> [] end",
    );
    assert!(
        nat_well_sorted_report(&thy).is_empty(),
        "the inlined `%i` is nat sorted"
    );
}

/// The parsed theory for `src`, as the wellformedness pass reads it.
fn parse(src: &str) -> p::Theory {
    tamarin_parser::parse_theory(src, &["diff"]).expect("parse")
}

/// The whole pre-translation report of a parsed theory.  [`check_theory`]
/// takes both representations of the same source, so the harness elaborates
/// the theory the way the drivers do.
fn check(parsed: &p::Theory) -> WfReport {
    let elaborated = crate::elaborate::elaborate(parsed).expect("elaborate");
    check_theory(&elaborated, parsed)
}

/// Return the single `WfError` whose topic matches `topic`.
fn only(report: &WfReport, topic: &str) -> String {
    let hits: Vec<&WfError> = report.iter().filter(|e| e.topic == topic).collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one {:?} entry, got {:?}",
        topic,
        report
    );
    hits[0].message.clone()
}

/// Probed against tamarin-prover v1.13.0 on `Out(<~k, ~'foo'>)`:
///   rule name uses the HS `quote` form (backtick + apostrophe) and the
///   fresh constant renders via `show (Name FreshName ..)` = `~'foo'`.
#[test]
fn fresh_public_constants_message_format() {
    let t = parse(
        "theory T begin \
            rule R: [ Fr(~k) ] --[ ]-> [ Out(<~k, ~'foo'>) ] end",
    );
    let msg = only(&check(&t), "Fresh public constants");
    assert_eq!(
        msg,
        "Fresh public constants\n======================\n\n  \
             rule `R': fresh public constants are not allowed: ~'foo'"
    );
}
