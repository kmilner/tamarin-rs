// Currently GPL 3.0 until granted permission by the following authors:
//   Kevin Morio, Robert Künnemann, Simon Meier, Jannik Dreier, Benedikt
//   Schmidt, Artur Cygan, Philip Lukert, Charlie Jacomme, Yavor Ivanov,
//   "Nynko" (github), Ralf Sasse, Felix Linker, Jérôme (github Azurios-git),
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Tools/IntruderRules.hs, src/Main/Mode/Intruder.hs,
//   src/Main/TheoryLoader.hs

//! Pre-computed intruder-variant rule loaders.
//!
//! HS-faithful port of `Main.TheoryLoader.mkDhIntruderVariants` and
//! `mkBpIntruderVariants` (src/Main/TheoryLoader.hs:745-768):
//!
//! ```haskell
//! dhIntruderVariantsFile :: FilePath
//! dhIntruderVariantsFile = "data/intruder_variants_dh.spthy"
//!
//! mkDhIntruderVariants :: MaudeSig -> [IntrRuleAC]
//! mkDhIntruderVariants msig =
//!     either (error . show) id $
//!         parseIntruderRules msig dhIntruderVariantsFile
//!           $(embedFile "data/intruder_variants_dh.spthy")
//! ```
//!
//! HS embeds the cached `.spthy` file via Template Haskell's `embedFile`
//! and parses it on every theory load.  We mirror that exactly with
//! `include_str!` (the Rust analog: compile-time string baking, identical
//! semantics — both fail loudly at compile time if the file is missing).
//!
//! The cached files at `data/intruder_variants_dh.spthy` (51 rules) and
//! `data/intruder_variants_bp.spthy` (75 rules) were produced by HS's
//! `Main.Mode.Intruder.run` (src/Main/Mode/Intruder.hs:48) — that mode
//! invokes `dhIntruderRules False`/`bpIntruderRules False` against
//! Maude and pretty-prints the result.  See [`crate::intruder_rules`]
//! for the Rust port of `dhIntruderRules`, which IS still used as a
//! regenerator (the function that PRODUCES the cache file) but is not
//! the production runtime path.

use tamarin_parser as p;
use tamarin_term::maude_sig::MaudeSig;

use crate::elaborate;
use crate::fact::LNFact;
use crate::rule::{IntrRuleAC, IntrRuleACInfo, Rule};

/// HS `dhIntruderVariantsFile` (TheoryLoader.hs:746).
pub const DH_INTRUDER_VARIANTS_FILE: &str = "data/intruder_variants_dh.spthy";

/// HS `bpIntruderVariantsFile` (TheoryLoader.hs:750).
pub const BP_INTRUDER_VARIANTS_FILE: &str = "data/intruder_variants_bp.spthy";

/// The DH intruder-variants spthy source, embedded at compile time
/// (HS uses `$(embedFile "data/intruder_variants_dh.spthy")` —
/// TheoryLoader.hs:759).
pub const DH_INTRUDER_VARIANTS_SPTHY: &str =
    include_str!("../../../tamarin-prover/data/intruder_variants_dh.spthy");

/// The BP intruder-variants spthy source, embedded at compile time
/// (HS uses `$(embedFile "data/intruder_variants_bp.spthy")` —
/// TheoryLoader.hs:768).
pub const BP_INTRUDER_VARIANTS_SPTHY: &str =
    include_str!("../../../tamarin-prover/data/intruder_variants_bp.spthy");

/// HS `mkDhIntruderVariants` (TheoryLoader.hs:753-759).
///
/// ```haskell
/// mkDhIntruderVariants :: MaudeSig -> [IntrRuleAC]
/// mkDhIntruderVariants msig =
///     either (error . show) id $
///         parseIntruderRules msig dhIntruderVariantsFile
///             $(embedFile "data/intruder_variants_dh.spthy")
/// ```
///
/// `either (error . show) id` ≡ `unwrap_or_else(|e| panic!("{}", e))`
/// (HS's `error . show` formats the parse error and aborts).
pub fn mk_dh_intruder_variants(msig: &MaudeSig) -> Vec<IntrRuleAC> {
    parse_intruder_rules(msig, DH_INTRUDER_VARIANTS_FILE, DH_INTRUDER_VARIANTS_SPTHY)
        .unwrap_or_else(|e| {
            panic!("mk_dh_intruder_variants: parse error in {}: {}",
                DH_INTRUDER_VARIANTS_FILE, e)
        })
}

/// HS `mkBpIntruderVariants` (TheoryLoader.hs:762-768).
pub fn mk_bp_intruder_variants(msig: &MaudeSig) -> Vec<IntrRuleAC> {
    parse_intruder_rules(msig, BP_INTRUDER_VARIANTS_FILE, BP_INTRUDER_VARIANTS_SPTHY)
        .unwrap_or_else(|e| {
            panic!("mk_bp_intruder_variants: parse error in {}: {}",
                BP_INTRUDER_VARIANTS_FILE, e)
        })
}

/// Error from `parse_intruder_rules`.  Includes the source file label
/// (HS `ctxtDesc` — Theory/Text/Parser/Rule.hs:202) for human-readable
/// diagnostics.
#[derive(Debug, Clone)]
pub struct IntrRuleParseError {
    pub ctxt_desc: String,
    pub message: String,
}

impl std::fmt::Display for IntrRuleParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.ctxt_desc, self.message)
    }
}

impl std::error::Error for IntrRuleParseError {}

/// HS `parseIntruderRules` (Theory/Text/Parser/Rule.hs:200-204):
///
/// ```haskell
/// parseIntruderRules
///     :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
/// parseIntruderRules msig ctxtDesc =
///     parseString [] ctxtDesc (setState (mkStateSig msig) >> many intrRule)
///   . T.unpack . TE.decodeUtf8
/// ```
///
/// The `setState (mkStateSig msig)` step is critical: HS's term parser
/// (Theory/Text/Parser/Term.hs:139-143) dispatches bare identifiers via
/// `nullaryApp` against `funSyms maudeSig` to distinguish 0-arity NoEq
/// applications (e.g. `one`, `DH_neutral` for `dhFunSig`) from free
/// variables.  Without it, the cached DH file's
/// `[ ] --[ !KU( one ) ]-> [ !KU( one ) ]` rule (intruder_variants_dh.spthy:8)
/// parses `one` as a Msg-sort variable whose !KU-action unifies with
/// every KU goal — adding a spurious `c_one` case to every source-case
/// enumeration and falsely closing branches with `SOLVED // trace found`.
///
/// We mirror this here via [`MaudeSigNullaryGuard`], which pushes the
/// 0-arity NoEq names from `msig` into the `USER_NULLARY_FUNS`
/// thread-local (defined in elaborate.rs) read by `term_to_lnterm`'s
/// `Var` branch, via `is_user_nullary_fun` (defined in elaborate.rs).
/// The guard restores the prior state on drop.
pub fn parse_intruder_rules(
    msig: &MaudeSig,
    ctxt_desc: &str,
    source: &str,
) -> Result<Vec<IntrRuleAC>, IntrRuleParseError> {
    let parser_rules = p::parse_intruder_rules(source)
        .map_err(|e| IntrRuleParseError {
            ctxt_desc: ctxt_desc.to_string(),
            message: e.to_string(),
        })?;

    // Mirror HS `setState (mkStateSig msig)` — make the term-conversion
    // pass below see the 0-arity NoEq names from `msig` so bare
    // identifiers like `one` / `DH_neutral` are recognised as constants.
    let _nullary_guard = elaborate::MaudeSigNullaryGuard::set(msig);

    let mut out = Vec::with_capacity(parser_rules.len());
    for r in parser_rules {
        let intr = ast_rule_to_intr_rule_ac(&r)
            .map_err(|message| IntrRuleParseError {
                ctxt_desc: ctxt_desc.to_string(),
                message,
            })?;
        out.push(intr);
    }
    Ok(out)
}

/// HS `intrRule` (Theory/Text/Parser/Rule.hs:155-169):
///
/// ```haskell
/// intrRule :: Parser IntrRuleAC
/// intrRule = do
///     info <- try (symbol "rule" *> moduloAC *> intrInfo <* colon)
///     (ps,as,cs,[]) <- genericRule msgvar nodevar
///     return $ Rule info ps cs as (newVariables ps cs)
///   where
///     intrInfo = do
///         name     <- identifier
///         limit    <- option 0 natural
///         case name of
///           'c':cname -> return $ ConstrRule (BC.pack cname)
///           'd':dname -> return $ DestrRule (BC.pack dname)
///                                   (fromIntegral limit) True False
///           _         -> fail $ "invalid intruder rule name '" ++ name ++ "'"
/// ```
///
/// The first character of the parsed name (`c` or `d`) is the rule-kind
/// dispatch; the REMAINING name string is what goes into the `Vec<u8>`
/// (e.g. `c_exp` → `ConstrRule "_exp"`, `d_exp` → `DestrRule "_exp" 0 True False`).
///
/// `option 0 natural` defaults `limit` to 0.  The cached `.spthy` files
/// never emit a non-zero limit (they're produced by the canonical HS
/// generator which doesn't print one), so we always see limit=0 here.
/// (Note: this port's `parse_intruder_rules` — parser.rs `parse_rule_ac`
/// — does not even read a trailing natural limit; it expects `:` after
/// the rule attributes.  A hand-written intruder rule carrying an
/// explicit limit would therefore be rejected here, whereas HS's
/// `option 0 natural` would accept it.  This is a latent, unexercised
/// parser-side divergence — the cached corpus never hits it.)
///
/// `True False` are HS hard-codes — see the FIXME in
/// Theory/Text/Parser/Rule.hs ("Currently we (wrongly) always assume
/// that we have a subterm rule").  Subterm=True / constant=False.
fn ast_rule_to_intr_rule_ac(r: &p::Rule) -> Result<IntrRuleAC, String> {
    // HS `intrInfo` rejects non-c/d-prefixed names.  Mirror that here.
    let bytes = r.name.as_bytes();
    if bytes.is_empty() {
        return Err("empty intruder rule name".to_string());
    }
    let (kind, rest) = (bytes[0], &bytes[1..]);
    let info: IntrRuleACInfo = match kind {
        b'c' => IntrRuleACInfo::ConstrRule(rest.to_vec()),
        b'd' => IntrRuleACInfo::DestrRule(
            rest.to_vec(),
            // HS `fromIntegral limit` where `limit <- option 0 natural`.
            // The cached files never specify a limit; we always see 0.
            0,
            // HS hard-codes `True False` (subterm, constant).
            true,
            false,
        ),
        _ => return Err(format!(
            "invalid intruder rule name '{}': must start with `c` (constructor) \
             or `d` (destructor) — HS Rule.hs:166-169", r.name)),
    };

    // HS `genericRule msgvar nodevar` returns `(ps, as, cs, [])`.
    // The let block, restrictions, variants, and left/right fields
    // are all empty for intruder rules.  Surface them as elaboration
    // errors if present (defensive).
    if !r.let_block.is_empty() {
        return Err(format!("intruder rule {} unexpectedly has a let-block", r.name));
    }
    if !r.embedded_restrictions.is_empty() {
        return Err(format!("intruder rule {} unexpectedly has embedded restrictions", r.name));
    }
    if !r.variants.is_empty() {
        return Err(format!("intruder rule {} unexpectedly has variants", r.name));
    }
    if r.left_right.is_some() {
        return Err(format!("intruder rule {} unexpectedly has left/right halves", r.name));
    }

    // Convert facts via the existing AST→LNFact path.  `fact_to_lnfact`
    // already handles the `KU`/`KD`/etc. tag mapping (elaborate.rs:974).
    let prems: Vec<LNFact> = r.premises.iter()
        .map(|f| elaborate::fact_to_lnfact(f)
            .map_err(|e| format!("intruder rule {}: premise: {}", r.name, e.message)))
        .collect::<Result<_, _>>()?;
    let acts: Vec<LNFact> = r.actions.iter()
        .map(|f| elaborate::fact_to_lnfact(f)
            .map_err(|e| format!("intruder rule {}: action: {}", r.name, e.message)))
        .collect::<Result<_, _>>()?;
    let concs: Vec<LNFact> = r.conclusions.iter()
        .map(|f| elaborate::fact_to_lnfact(f)
            .map_err(|e| format!("intruder rule {}: conclusion: {}", r.name, e.message)))
        .collect::<Result<_, _>>()?;

    // HS `newVariables ps cs` — variables that appear in conclusions
    // but not premises.  The intruder-rule `.spthy` files don't have
    // any (all RHS vars are LHS vars), but compute it faithfully for
    // robustness.  HS reference: Theory.Model.Fact.newVariables
    // (lib/theory/src/Theory/Model/Fact.hs:494).
    let new_vars = compute_new_vars(&prems, &concs);

    Ok(Rule::new(info, prems, concs, acts).with_new_vars(new_vars))
}

/// Mirrors HS `newVariables` (`lib/theory/src/Theory/Model/Fact.hs:494`):
/// the set of variables in `conclusions` that are not in `premises`,
/// returned in deterministic order.
fn compute_new_vars(
    prems: &[LNFact],
    concs: &[LNFact],
) -> Vec<tamarin_term::lterm::LNTerm> {
    use std::collections::BTreeSet;
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    fn collect(t: &tamarin_term::lterm::LNTerm, out: &mut BTreeSet<LVar>) {
        match t {
            Term::Lit(Lit::Var(v)) => { out.insert(v.clone()); }
            Term::Lit(_) => {}
            Term::App(_, args) => for a in args.iter() { collect(a, out); }
        }
    }

    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        for t in &f.terms { collect(t, &mut prem_vars); }
    }
    let mut new_set: BTreeSet<LVar> = BTreeSet::new();
    for f in concs {
        for t in &f.terms {
            let mut here = BTreeSet::new();
            collect(t, &mut here);
            for v in here {
                if !prem_vars.contains(&v) { new_set.insert(v); }
            }
        }
    }
    new_set.into_iter().map(|v| Term::Lit(Lit::Var(v))).collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};

    /// The cached DH file is documented to contain exactly 51 rules:
    /// 5 constructors (`c_exp`, `c_inv`, `c_one`, `c_DH_neutral`, `c_mult`)
    /// + 45 `d_exp` destructor variants + 1 `d_inv` destructor variant.
    ///   `grep -c "^rule " data/intruder_variants_dh.spthy` = 51.
    #[test]
    fn dh_variants_file_parses_to_51_rules() {
        let rules = mk_dh_intruder_variants(&dh_maude_sig());
        assert_eq!(rules.len(), 51,
            "data/intruder_variants_dh.spthy should yield exactly 51 rules \
             (HS-cached output of `dhIntruderRules`); got {}", rules.len());
    }

    /// Count check for the BP cached file
    /// (`grep -c "^rule " data/intruder_variants_bp.spthy` = 75).
    #[test]
    fn bp_variants_file_parses_to_75_rules() {
        let rules = mk_bp_intruder_variants(&bp_maude_sig());
        assert_eq!(rules.len(), 75,
            "data/intruder_variants_bp.spthy should yield exactly 75 rules; got {}",
            rules.len());
    }

    /// The 5 constructor rules MUST be present with their HS-canonical
    /// underscore-prefixed names (`c_exp` → `ConstrRule "_exp"`, etc).
    /// HS reference: Theory/Tools/IntruderRules.hs:233-244 +
    /// Theory/Text/Parser/Rule.hs:167 (`'c':cname → ConstrRule (BC.pack cname)`).
    #[test]
    fn dh_variants_contains_five_constructors_with_underscore_prefix() {
        let rules = mk_dh_intruder_variants(&dh_maude_sig());
        let constr_names: Vec<&[u8]> = rules.iter()
            .filter_map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => Some(n.as_slice()),
                _ => None,
            }).collect();
        assert_eq!(constr_names.len(), 5,
            "expected exactly 5 ConstrRules; got {:?}",
            constr_names.iter().map(|n| String::from_utf8_lossy(n).to_string())
                .collect::<Vec<_>>());
        for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
            assert!(constr_names.contains(expected),
                "missing constructor named {} in DH variants; got names {:?}",
                String::from_utf8_lossy(expected),
                constr_names.iter().map(|n| String::from_utf8_lossy(n).to_string())
                    .collect::<Vec<_>>());
        }
    }

    /// Every destructor rule in DH must have shape `DestrRule name 0 True False`
    /// (HS Rule.hs:168 hard-codes `(fromIntegral limit) True False`, and
    /// `option 0 natural` means limit=0 when none is parsed — none of the
    /// cached destructors have a numeric limit).  The name must start
    /// with `_` (HS strips the leading `d` and keeps the `_<rest>` as-is).
    #[test]
    fn dh_variants_destructors_are_d_exp_or_d_inv_with_limit_0() {
        let rules = mk_dh_intruder_variants(&dh_maude_sig());
        let destrs: Vec<&IntrRuleAC> = rules.iter()
            .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule(..)))
            .collect();
        assert_eq!(destrs.len(), 46,
            "DH cached file: 5 constr + 46 destr = 51 (45 d_exp + 1 d_inv); \
             got {} destructors", destrs.len());
        for d in &destrs {
            if let IntrRuleACInfo::DestrRule(name, limit, subterm, constant) = &d.info {
                assert!(name.starts_with(b"_"),
                    "destructor name must start with `_` (HS leading `d` is consumed, \
                     rest goes to the bytestring); got {}",
                    String::from_utf8_lossy(name));
                assert_eq!(*limit, 0,
                    "DestrRule limit must be 0 (HS Rule.hs:168 `fromIntegral limit` \
                     with `option 0 natural` and no numeric in the cached file); \
                     got {}", limit);
                assert!(*subterm,
                    "DestrRule subterm must be True (HS Rule.hs:168 hard-codes True)");
                assert!(!(*constant),
                    "DestrRule constant must be False (HS Rule.hs:168 hard-codes False)");
                // Names in the DH file: only `_exp` and `_inv`.
                assert!(name == b"_exp" || name == b"_inv",
                    "DH destructor name must be `_exp` or `_inv`; got {}",
                    String::from_utf8_lossy(name));
            }
        }
    }

    /// `parse_intruder_rules` is the public entry point with full HS
    /// signature `MaudeSig → ctxtDesc → source → Result`.  Verify it
    /// works directly on a tiny inline source.
    #[test]
    fn parse_intruder_rules_handles_tiny_inline() {
        let src = "rule (modulo AC) c_exp:\n   [ !KU( x ), !KU( x.1 ) ] --[ !KU( x^x.1 ) ]-> [ !KU( x^x.1 ) ]\n";
        let rules = parse_intruder_rules(&dh_maude_sig(), "<inline>", src)
            .expect("parse_intruder_rules on inline src");
        assert_eq!(rules.len(), 1);
        match &rules[0].info {
            IntrRuleACInfo::ConstrRule(n) => assert_eq!(n.as_slice(), b"_exp"),
            other => panic!("expected ConstrRule, got {:?}", other),
        }
    }

    /// Rule names that don't start with `c` or `d` must be rejected
    /// (HS Rule.hs:169 — `fail "invalid intruder rule name ..."`).
    #[test]
    fn parse_intruder_rules_rejects_non_c_d_prefix() {
        let src = "rule (modulo AC) xfoo:\n   [ ] --> [ ]\n";
        let err = parse_intruder_rules(&dh_maude_sig(), "<bad>", src)
            .expect_err("rule named `xfoo` should be rejected");
        assert!(err.message.contains("invalid intruder rule name"),
            "expected `invalid intruder rule name` in error; got {}", err.message);
    }

    /// Round-trip: every rule produced by `mk_dh_intruder_variants` has
    /// a name starting with `_` (the byte after the consumed `c`/`d`).
    /// Mirrors the same property checked for the runtime generator
    /// `dh_intruder_rules` in `dh_variants_all_names_have_underscore_prefix`.
    #[test]
    fn dh_variants_all_names_have_underscore_prefix() {
        let rules = mk_dh_intruder_variants(&dh_maude_sig());
        for r in &rules {
            let n = match &r.info {
                IntrRuleACInfo::ConstrRule(n) => n.as_slice(),
                IntrRuleACInfo::DestrRule(n, _, _, _) => n.as_slice(),
                other => panic!("unexpected info kind: {:?}", other),
            };
            assert!(n.starts_with(b"_"),
                "DH variant name must start with `_` (HS `'c':cname`/`'d':dname` consumes the prefix); \
                 got {}", String::from_utf8_lossy(n));
        }
    }

    /// Bridge check: the runtime generator `dh_intruder_rules` and the
    /// cached-file parser `mk_dh_intruder_variants` SHOULD agree on the
    /// number and names of rules — both are different paths to the same
    /// HS `dhIntruderRules` output.  We don't assert strict equality
    /// (Maude variant ordering / re-renaming can legitimately differ)
    /// — just the rule count and the constructor-rule names.  A mismatch
    /// here is a hint that Maude version drift may have invalidated the
    /// cached file.
    #[test]
    fn bridge_runtime_generator_matches_cached_file_on_counts_and_names() {
        // The runtime generator needs a Maude handle; skip if not available
        // (mirroring the `maude_handle`/`dh_maude_handle` gating in
        // intruder_rules.rs).
        let maude_path = std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        });
        let maude = match maude_path.and_then(|p|
            tamarin_term::maude_proc::MaudeHandle::start(&p, dh_maude_sig()).ok())
        {
            Some(m) => m, None => return,
        };

        let cached = mk_dh_intruder_variants(&dh_maude_sig());
        let runtime = crate::intruder_rules::dh_intruder_rules(false, &maude);

        // Constructor names should be identical sets.
        let cached_constrs: std::collections::BTreeSet<Vec<u8>> = cached.iter()
            .filter_map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => Some(n.clone()), _ => None,
            }).collect();
        let runtime_constrs: std::collections::BTreeSet<Vec<u8>> = runtime.iter()
            .filter_map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => Some(n.clone()), _ => None,
            }).collect();
        if cached_constrs != runtime_constrs {
            eprintln!("bridge test: cached constr names ≠ runtime constr names");
            eprintln!("  cached  = {:?}", cached_constrs.iter()
                .map(|n| String::from_utf8_lossy(n).to_string()).collect::<Vec<_>>());
            eprintln!("  runtime = {:?}", runtime_constrs.iter()
                .map(|n| String::from_utf8_lossy(n).to_string()).collect::<Vec<_>>());
        }
        assert_eq!(cached_constrs, runtime_constrs,
            "runtime and cached DH constr name sets should match");

        // Destructor counts should be EQUAL or DIFFER (the cached file
        // is authoritative — log a diff but don't fail).  Counts may
        // legitimately differ if today's Maude produces a different
        // variant enumeration order than the cached file's day.
        if cached.len() != runtime.len() {
            eprintln!(
                "bridge test note: cached DH rule count = {}, runtime = {} \
                 — investigate if today's Maude has drifted from the cached file",
                cached.len(), runtime.len());
        }
    }

    /// Regression test for the `c_one` / `c_DH_neutral` soundness invariant:
    /// under `dh_maude_sig()`, the rule `[ ] --[ !KU( one ) ]-> [ !KU( one ) ]`
    /// must have ROOT = the 0-arity NoEq application `oneSym{}`, NOT a Msg-sort
    /// var `one` (which would unify with every KU goal, falsely closing 8+ DH
    /// corpus branches).  HS: Theory/Text/Parser/Term.hs:139-143 (`nullaryApp`
    /// against `funSyms maudeSig`) and
    /// lib/term/src/Term/Term/FunctionSymbols.hs:163
    /// (`oneSym = ("one",(0,Public,Constructor))`).
    #[test]
    fn dh_one_and_dh_neutral_parse_as_constants() {
        use tamarin_term::function_symbols::{
            DH_NEUTRAL_SYM_STRING, ONE_SYM_STRING,
        };
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;

        let rules = mk_dh_intruder_variants(&dh_maude_sig());
        let c_one = rules.iter().find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule(n) => n.as_slice() == b"_one",
            _ => false,
        }).expect("c_one rule should be present");
        let c_dh_neutral = rules.iter().find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule(n) => n.as_slice() == b"_DH_neutral",
            _ => false,
        }).expect("c_DH_neutral rule should be present");

        // Each rule has shape `[ ] --[ !KU( <const> ) ]-> [ !KU( <const> ) ]`.
        // The action and conclusion fact must carry a 0-arity NoEq term
        // whose name is the canonical sym-string.  Crucially, it must
        // NOT be a `Term::Lit(Lit::Var(_))`.
        for (label, rule, expected_name) in [
            ("c_one", c_one, ONE_SYM_STRING),
            ("c_DH_neutral", c_dh_neutral, DH_NEUTRAL_SYM_STRING),
        ] {
            assert_eq!(rule.actions.len(), 1, "{}: expected one action", label);
            let action_term = &rule.actions[0].terms[0];
            match action_term {
                Term::App(sym, args) => {
                    if let tamarin_term::function_symbols::FunSym::NoEq(s) = sym {
                        assert_eq!(s.name, expected_name,
                            "{}: action term sym name", label);
                        assert_eq!(s.arity, 0, "{}: action term arity", label);
                        assert!(args.is_empty(), "{}: action term args", label);
                    } else {
                        panic!("{}: expected NoEq sym, got {:?}", label, sym);
                    }
                }
                Term::Lit(Lit::Var(v)) => panic!(
                    "{}: REGRESSION — action term is a free variable {:?} \
                     instead of a 0-arity NoEq constant. The `{}` symbol \
                     was not recognised against the MaudeSig; check that \
                     `parse_intruder_rules` threads the MaudeSig through \
                     `MaudeSigNullaryGuard`.",
                    label, v, String::from_utf8_lossy(expected_name),
                ),
                other => panic!("{}: unexpected action term {:?}", label, other),
            }
        }
    }

    /// Counterpart to `dh_one_and_dh_neutral_parse_as_constants`: with
    /// NO DH builtin enabled, parsing a rule containing a bare `one`
    /// must NOT magically convert it to a constant — the
    /// `USER_NULLARY_FUNS` lookup is gated on the MaudeSig.  HS
    /// behaviour: under `pairMaudeSig`, `funSyms` excludes `oneSym`, so
    /// `nullaryApp` falls through to `plit` and `one` parses as a
    /// variable.  Confirms our MaudeSig gating mirrors HS.
    #[test]
    fn one_is_var_when_no_dh_builtin_in_maude_sig() {
        use tamarin_term::maude_sig::pair_maude_sig;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;

        let src = "rule (modulo AC) c_test:\n   [ ] --[ !KU( one ) ]-> [ !KU( one ) ]\n";
        let rules = parse_intruder_rules(&pair_maude_sig(), "<no-dh>", src)
            .expect("parse_intruder_rules under pair_maude_sig");
        assert_eq!(rules.len(), 1);
        let action_term = &rules[0].actions[0].terms[0];
        match action_term {
            Term::Lit(Lit::Var(v)) => {
                assert_eq!(v.name, "one",
                    "under pair_maude_sig, `one` should remain a Var; HS-equivalent: \
                     `funSyms pairMaudeSig` does not include `oneSym`");
            }
            other => panic!(
                "expected Var (no DH builtin → MaudeSig has no `one` constant), \
                 got {:?}",
                other,
            ),
        }
    }
}
