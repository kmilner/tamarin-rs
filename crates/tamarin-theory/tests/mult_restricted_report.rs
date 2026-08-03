// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term.hs,
//   lib/theory/src/Theory/Tools/Wellformedness.hs

//! Byte-pins HS `multRestrictedReport'` (Wellformedness.hs:1047-1099) — both
//! of its triggers, the sort filter on the rhs-only variables, and the
//! silence that the DH corpus depends on.
//!
//! The check fires when `restrictedFailures ru` is not `([],[])`, i.e. when
//! the rule's CONCLUSIONS carry a `*`-headed sub-term, or when abstracting
//! the reducible-headed PREMISE sub-terms (against the elaborated signature's
//! `irreducibleFunSyms`) leaves non-public variables that occur only in the
//! conclusions.  The second trigger is invisible on the surface syntax: it
//! needs the reducible/irreducible classification and the `x.<n>` fresh
//! variables `abstractRule` mints.
//!
//! Expected strings are the pinned oracle's bytes (Git revision ef3f0468).

use tamarin_parser::parse_theory;
use tamarin_theory::mult_restricted::mult_restricted_report;
use tamarin_theory::pretty_theory::format_wf_block;

/// The rendered `/* WARNING … */` block for a theory's multiplication-
/// restriction report, or `None` when the check stays silent.
fn block(src: &str) -> Option<String> {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let errs = mult_restricted_report(&thy, &elaborated, &elaborated.signature.maude_sig);
    if errs.is_empty() {
        return None;
    }
    Some(format_wf_block(&errs))
}

const HEADER: &str = "/*\nWARNING: the following wellformedness checks failed!\n\n\
                      Multiplication restriction of rules\n\
                      ===================================\n\n";

/// The second trigger, with no multiplication anywhere: `fst` is reducible,
/// so `abstractTerm` replaces the whole premise term with a fresh `x.1` and
/// `x` stops being bound by the left-hand side.  Only the
/// `unbound ruAbstr \\ unbound ru` half of `restrictedFailures` fires, so the
/// entry ends with the "Variables that occur only in rhs" line alone —
/// HS's `above_ p _ Empty = p` drops the absent multiplication line without
/// leaving a blank behind it.
#[test]
fn abstraction_leaving_rhs_only_vars_fires_without_any_multiplication() {
    let src = "theory MrUnbound begin\n\
               rule R1: [ In( fst(x) ) ] --[ Go( x ) ]-> [ Out( x ) ]\n\
               end\n";
    assert_eq!(
        block(src).expect("rhs-only var must be reported"),
        format!(
            "{HEADER}  \
             The following rule is not multiplication restricted:\n    \
             rule (modulo E) R1:\n       \
             [ In( fst(x) ) ] --[ Go( x ) ]-> [ Out( x ) ]\n  \n  \
             After replacing reducible function symbols in lhs with variables:\n    \
             rule (modulo E) R1:\n       \
             [ In( x.1 ) ] --[ Go( x ) ]-> [ Out( x ) ]\n  \n    \
             Variables that occur only in rhs:  x\n*/"
        )
    );
}

/// Both halves of `restrictedFailures` at once: the conclusion carries a
/// product AND the abstraction orphans `x`.  The two lines are adjacent —
/// the `text ""` separators sit only after the two rule dumps.  The rule
/// dump itself wraps here, which the theory-body echo of the same rule does
/// not: the wellformedness comment is rendered at HughesPJ's default
/// 100/67, the theory body at the console's 110/73.
#[test]
fn both_failure_kinds_print_their_lines_back_to_back() {
    let src = "theory MrBoth begin\n\
               builtins: diffie-hellman\n\
               rule R2:\n\
               \x20 [ In( fst(x) ), Fr(~a), Fr(~b) ] --[ Go( x ) ]-> [ Out( <x, (~a*~b)> ) ]\n\
               end\n";
    assert_eq!(
        block(src).expect("both triggers must be reported"),
        format!(
            "{HEADER}  \
             The following rule is not multiplication restricted:\n    \
             rule (modulo E) R2:\n       \
             [ In( fst(x) ), Fr( ~a ), Fr( ~b ) ]\n      \
             --[ Go( x ) ]->\n       \
             [ Out( <x, (~a*~b)> ) ]\n  \n  \
             After replacing reducible function symbols in lhs with variables:\n    \
             rule (modulo E) R2:\n       \
             [ In( x.1 ), Fr( ~a ), Fr( ~b ) ]\n      \
             --[ Go( x ) ]->\n       \
             [ Out( <x, (~a*~b)> ) ]\n  \n    \
             Terms with multiplication:  (~a*~b)\n    \
             Variables that occur only in rhs:  x\n*/"
        )
    );
}

/// `unbound` drops `LSortPub` variables (`RPub` is silent), the abstraction
/// memoises per TERM so the repeated `fst(z)` shares one `x.1` while
/// `snd(w)` takes the next index, and `prettyVarList` lists the survivors in
/// `Ord LVar` order (`w` before `z`, both at index 0, by name).  Two
/// offending rules also exercise `prettyWfErrorReport`'s per-group
/// two-space blank separator.
#[test]
fn rhs_only_vars_drop_pub_sorts_and_share_one_abstraction_per_term() {
    let src = "theory MrSorts begin\n\
               rule RFresh: [ In( fst(~x) ) ] --[ Go( 'a' ) ]-> [ Out( ~x ) ]\n\
               rule RPub: [ In( fst($p) ) ] --[ Go( 'b' ) ]-> [ Out( $p ) ]\n\
               rule RShared:\n\
               \x20 [ In( fst(z) ), In( fst(z) ), In( snd(w) ) ] --[ Go( 'c' ) ]-> [ Out( <z, w> ) ]\n\
               end\n";
    assert_eq!(
        block(src).expect("two rules must be reported"),
        format!(
            "{HEADER}  \
             The following rule is not multiplication restricted:\n    \
             rule (modulo E) RFresh:\n       \
             [ In( fst(~x) ) ] --[ Go( 'a' ) ]-> [ Out( ~x ) ]\n  \n  \
             After replacing reducible function symbols in lhs with variables:\n    \
             rule (modulo E) RFresh:\n       \
             [ In( x.1 ) ] --[ Go( 'a' ) ]-> [ Out( ~x ) ]\n  \n    \
             Variables that occur only in rhs:  ~x\n  \n  \
             The following rule is not multiplication restricted:\n    \
             rule (modulo E) RShared:\n       \
             [ In( fst(z) ), In( fst(z) ), In( snd(w) ) ]\n      \
             --[ Go( 'c' ) ]->\n       \
             [ Out( <z, w> ) ]\n  \n  \
             After replacing reducible function symbols in lhs with variables:\n    \
             rule (modulo E) RShared:\n       \
             [ In( x.1 ), In( x.1 ), In( x.2 ) ]\n      \
             --[ Go( 'c' ) ]->\n       \
             [ Out( <z, w> ) ]\n  \n    \
             Variables that occur only in rhs:  w, z\n*/"
        )
    );
}

/// `multTerms` reads the CONCLUSIONS only, and an exponentiation keeps its
/// nested `exp` shape in the E-rule (`fAppExp` is a plain `fAppNoEq`,
/// Term/Term.hs:161-164) — no `Mult` node reaches the conclusions.  A rule
/// whose only product sits in an ACTION is therefore silent, which is what
/// keeps the whole DH / bilinear corpus free of this topic.
#[test]
fn a_multiplication_restricted_dh_rule_stays_silent() {
    let src = "theory MrSilent begin\n\
               builtins: diffie-hellman\n\
               rule R3: [ Fr(~a), Fr(~b) ] --[ Test(~a*~b) ]-> [ Out( 'g'^~a^~b ) ]\n\
               end\n";
    assert_eq!(block(src), None);
}

/// Every product in a conclusion is listed, in the conclusion's own term
/// order, through `prettyLNTermList = fsep . punctuate comma . map
/// prettyLNTerm` (Wellformedness.hs:146-147); `multTerms` stops at a `Mult`
/// node, so the operands of a listed product never reappear.
#[test]
fn every_conclusion_product_is_listed_in_term_order() {
    let src = "theory MrList begin\n\
               builtins: diffie-hellman\n\
               rule RC:\n\
               \x20 [ Fr(~c), Fr(~d) ] --[ Go( 'c' ) ]-> [ Out( <(~c*~d), (~d*~c*~c)> ) ]\n\
               end\n";
    let rendered = block(src).expect("products must be reported");
    assert!(
        rendered.ends_with("\n    Terms with multiplication:  (~c*~d), (~c*~c*~d)\n*/"),
        "block: {rendered}"
    );
}
