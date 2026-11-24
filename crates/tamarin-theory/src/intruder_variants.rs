// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Pre-computed intruder-variant rule loaders: HS `mkDhIntruderVariants` and
//! `mkBpIntruderVariants` (src/Main/TheoryLoader.hs), which parse the
//! embedded `data/intruder_variants_{dh,bp}.spthy` on every theory load.
//!
//! The committed BP file holds 75 rules, one more than
//! [`crate::intruder_rules::bp_intruder_rules`] (and `tamarin-prover
//! variants` at the pinned revision) regenerates: `minimizeIntruderRules`
//! now subsumes one `d_em` variant the file still lists.  Both provers parse
//! the committed file, so proving is unaffected.

use tamarin_parser as p;
use tamarin_term::function_symbols::FunSym;
use tamarin_term::maude_sig::MaudeSig;

use crate::elaborate;
use crate::fact::LNFact;
use crate::intruder_rules::show_fun_sym_name;
use crate::rule::{IntrRuleAC, IntrRuleACInfo, Rule};

/// HS `dhIntruderVariantsFile` (TheoryLoader.hs).
pub const DH_INTRUDER_VARIANTS_FILE: &str = "data/intruder_variants_dh.spthy";

/// HS `bpIntruderVariantsFile` (TheoryLoader.hs).
pub const BP_INTRUDER_VARIANTS_FILE: &str = "data/intruder_variants_bp.spthy";

/// The embedded DH intruder-variants file (HS `embedFile`).
pub const DH_INTRUDER_VARIANTS_SPTHY: &str =
    include_str!("../../../tamarin-prover/data/intruder_variants_dh.spthy");

/// The embedded BP intruder-variants file (HS `embedFile`).
pub const BP_INTRUDER_VARIANTS_SPTHY: &str =
    include_str!("../../../tamarin-prover/data/intruder_variants_bp.spthy");

/// HS `mkDhIntruderVariants` (TheoryLoader.hs); a parse error aborts, as
/// HS's `either (error . show) id` does.
pub fn mk_dh_intruder_variants(msig: &MaudeSig) -> Vec<IntrRuleAC> {
    parse_intruder_rules(msig, DH_INTRUDER_VARIANTS_FILE, DH_INTRUDER_VARIANTS_SPTHY)
        .unwrap_or_else(|e| {
            panic!(
                "mk_dh_intruder_variants: parse error in {}: {}",
                DH_INTRUDER_VARIANTS_FILE, e
            )
        })
}

/// HS `mkBpIntruderVariants` (TheoryLoader.hs).
pub fn mk_bp_intruder_variants(msig: &MaudeSig) -> Vec<IntrRuleAC> {
    parse_intruder_rules(msig, BP_INTRUDER_VARIANTS_FILE, BP_INTRUDER_VARIANTS_SPTHY)
        .unwrap_or_else(|e| {
            panic!(
                "mk_bp_intruder_variants: parse error in {}: {}",
                BP_INTRUDER_VARIANTS_FILE, e
            )
        })
}

/// Error from `parse_intruder_rules`.  Includes the source file label
/// (HS `ctxtDesc` — Theory/Text/Parser/Rule.hs) for human-readable
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

/// HS `parseIntruderRules` (Theory/Text/Parser/Rule.hs):
///
/// ```haskell
/// parseIntruderRules
///     :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
/// parseIntruderRules msig ctxtDesc =
///     parseString [] ctxtDesc (setState (mkStateSig msig) >> many intrRule)
///   . T.unpack . TE.decodeUtf8
/// ```
///
/// The signature lets the term parser read nullary symbols such as `one`
/// as applications, not variables (`nullaryApp`, Theory/Text/Parser/Term.hs).
pub fn parse_intruder_rules(
    msig: &MaudeSig,
    ctxt_desc: &str,
    source: &str,
) -> Result<Vec<IntrRuleAC>, IntrRuleParseError> {
    let parser_rules = p::parse_intruder_rules(msig, source).map_err(|e| IntrRuleParseError {
        ctxt_desc: ctxt_desc.to_string(),
        message: e.to_string(),
    })?;

    let mut out = Vec::with_capacity(parser_rules.len());
    for r in parser_rules {
        let intr = ast_rule_to_intr_rule_ac(msig, &r).map_err(|message| IntrRuleParseError {
            ctxt_desc: ctxt_desc.to_string(),
            message,
        })?;
        out.push(intr);
    }
    Ok(out)
}

/// HS `lookupFun` (Theory/Text/Parser/Rule.hs): the first symbol of
/// `knownFuns = S.toList (funSyms msig)` whose `showFunSymName` is `f`.
fn lookup_fun(msig: &MaudeSig, f: &str) -> Result<FunSym, String> {
    msig.fun_syms
        .iter()
        .copied()
        .find(|g| show_fun_sym_name(g) == f)
        .ok_or_else(|| {
            format!(
                "Failed parsing intruder rule name: no function named '{}' found in the signature (symbols: {})",
                f,
                msig.fun_syms
                    .iter()
                    .map(show_fun_sym_name)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
}

/// HS `constrNameFunc` (Theory/Text/Parser/Rule.hs): recover the function
/// names encoded in a destructor rule name.  Splits on `'_'`, drops the
/// leading empty segment (the name starts with an underscore), then drops
/// the LEADING purely-numeric position segments (`supprPos` via
/// `readMaybe :: Maybe Int`); errors on an empty result.
///
/// The split is unconditional, so a function symbol whose own name contains
/// `'_'` decomposes into several segments that [`lookup_fun`] cannot resolve
/// — see the FIXME beside `name_decompose` in Theory/Text/Parser/Rule.hs
/// ("there can be underscores in the name of a function").  Dormant for the
/// two cached files, which only name builtin DH/BP symbols.
fn constr_name_func(name: &str) -> Result<Vec<&str>, String> {
    // `tail . T.split (== '_')`, then `supprPos` (remove position
    // information from the rule name).
    let names: Vec<&str> = name
        .split('_')
        .skip(1)
        .skip_while(|seg| seg.parse::<i64>().is_ok())
        .collect();
    if names.is_empty() {
        return Err("Failed parsing intruder rule name: empty name".to_string());
    }
    Ok(names)
}

/// HS `intrRule` (Theory/Text/Parser/Rule.hs):
///
/// ```haskell
/// intrRule :: Parser IntrRuleAC
/// intrRule = do
///     (name, info)  <- try (symbol "rule" *> moduloAC *> intrInfo <* colon)
///     (ps,as,cs,[]) <- genericRule msgvar nodevar
///     return $ Rule info ps cs as (newVariables ps cs)
///   where
///     intrInfo = do
///         name  <- identifier
///         limit <- option 0 natural
///         msig  <- sig <$> getState
///         let knownFuns = S.toList (funSyms msig)
///         case name of
///           'c':cname -> return (cname, ConstrRule (BC.pack cname)
///                                         (lookupFun knownFuns $ tail cname))
///           'd':dname -> return (dname, DestrRule (BC.pack dname)
///                                         (fromIntegral limit) True False
///                                         (map (lookupFun knownFuns) (constrNameFunc dname)))
/// ```
///
/// The first character of the parsed name (`c` or `d`) is the rule-kind
/// dispatch; the REMAINING name string is what goes into the `Vec<u8>`
/// (e.g. `c_exp` → `ConstrRule "_exp" (NoEq expSym)`, `d_exp` →
/// `DestrRule "_exp" 0 True False [NoEq expSym]`).  The attached function
/// symbols are resolved against the signature: constructors via the name
/// after the underscore (`tail cname`), destructors via `constrNameFunc`
/// (split on `'_'`, position segments stripped).
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
fn ast_rule_to_intr_rule_ac(msig: &MaudeSig, r: &p::Rule) -> Result<IntrRuleAC, String> {
    // HS `intrInfo` rejects non-c/d-prefixed names.  Mirror that here.
    let bytes = r.name.as_bytes();
    if bytes.is_empty() {
        return Err("empty intruder rule name".to_string());
    }
    let (kind, rest) = (bytes[0], &bytes[1..]);
    let info: IntrRuleACInfo = match kind {
        b'c' => {
            // `lookupFun knownFuns $ tail cname` — cname is `_<fun>`, so
            // `tail` strips the leading underscore.
            let cname = &r.name[1..];
            let f = lookup_fun(msig, cname.get(1..).unwrap_or(""))?;
            IntrRuleACInfo::ConstrRule {
                name: rest.to_vec(),
                fun: f,
            }
        }
        b'd' => {
            let dname = &r.name[1..];
            let funs = constr_name_func(dname)?
                .into_iter()
                .map(|n| lookup_fun(msig, n))
                .collect::<Result<Vec<_>, _>>()?;
            IntrRuleACInfo::DestrRule {
                name: rest.to_vec(),
                // HS `fromIntegral limit` where `limit <- option 0 natural`.
                // The cached files never specify a limit; we always see 0.
                remaining_applications: 0,
                // HS hard-codes `True False` (subterm, constant).
                rhs_is_proper_subterm: true,
                rhs_is_constant: false,
                funs,
            }
        }
        _ => {
            return Err(format!(
                "invalid intruder rule name '{}': must start with `c` (constructor) \
             or `d` (destructor)",
                r.name
            ))
        }
    };

    // HS `genericRule msgvar nodevar` returns `(ps, as, cs, [])`.
    // The restrictions, variants, and left/right fields are all empty for
    // intruder rules.  Surface them as elaboration errors if present
    // (defensive).
    if !r.embedded_restrictions.is_empty() {
        return Err(format!(
            "intruder rule {} unexpectedly has embedded restrictions",
            r.name
        ));
    }
    if !r.variants.is_empty() {
        return Err(format!(
            "intruder rule {} unexpectedly has variants",
            r.name
        ));
    }
    if r.left_right.is_some() {
        return Err(format!(
            "intruder rule {} unexpectedly has left/right halves",
            r.name
        ));
    }

    // Convert facts via the existing AST→LNFact path.  `fact_to_lnfact`
    // already handles the `KU`/`KD`/etc. tag mapping
    // (`elaborate::fact_to_lnfact`).
    let prems: Vec<LNFact> = r
        .premises
        .iter()
        .map(|f| {
            elaborate::fact_to_lnfact(f, msig)
                .map_err(|e| format!("intruder rule {}: premise: {}", r.name, e.message))
        })
        .collect::<Result<_, _>>()?;
    let acts: Vec<LNFact> = r
        .actions
        .iter()
        .map(|f| {
            elaborate::fact_to_lnfact(f, msig)
                .map_err(|e| format!("intruder rule {}: action: {}", r.name, e.message))
        })
        .collect::<Result<_, _>>()?;
    let concs: Vec<LNFact> = r
        .conclusions
        .iter()
        .map(|f| {
            elaborate::fact_to_lnfact(f, msig)
                .map_err(|e| format!("intruder rule {}: conclusion: {}", r.name, e.message))
        })
        .collect::<Result<_, _>>()?;

    // HS `newVariables ps cs` — variables that appear in conclusions
    // but not premises.  The intruder-rule `.spthy` files don't have
    // any (all RHS vars are LHS vars), but compute it faithfully for
    // robustness.  HS reference: Theory.Model.Fact.newVariables
    // (lib/theory/src/Theory/Model/Fact.hs).
    let new_vars = crate::fact::new_variables(&prems, &concs);

    Ok(Rule::new(info, prems, concs, acts).with_new_vars(new_vars))
}

/// Elaborate one top-level `rule (modulo AC)` parsed in an ordinary theory.
pub(crate) fn intr_rule_from_ast(msig: &MaudeSig, r: &p::Rule) -> Result<IntrRuleAC, String> {
    ast_rule_to_intr_rule_ac(msig, r)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "intruder_variants_tests.rs"]
mod tests;
