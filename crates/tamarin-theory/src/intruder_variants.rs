// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! `Main.Mode.Intruder.run` (src/Main/Mode/Intruder.hs:43-63, see line 48) — that mode
//! invokes `dhIntruderRules False`/`bpIntruderRules False` against
//! Maude and pretty-prints the result.  See [`crate::intruder_rules`]
//! for the Rust port of `dhIntruderRules`, which IS still used as a
//! regenerator (the function that PRODUCES the cache file) but is not
//! the production runtime path.
//!
//! The committed BP cache holds 75 rules, one more than the regenerator
//! emits: `minimizeIntruderRules` (IntruderRules.hs:190-208) subsumes
//! rules via the Maude-backed `equalDuplicateRuleUpToRenaming` /
//! `equalSubsetRuleUpToRenaming`, collapsing one `d_em` variant that the
//! cached file still lists, so `tamarin-prover variants` on the pinned
//! upstream tree emits 74 BP rules.  Both HS and RS parse the committed
//! 75 rules on every theory load, so the two stay byte-identical in
//! production; the divergence is confined to the regenerator.

use tamarin_parser as p;
use tamarin_term::function_symbols::FunSym;
use tamarin_term::maude_sig::MaudeSig;

use crate::elaborate;
use crate::fact::LNFact;
use crate::intruder_rules::show_fun_sym_name;
use crate::rule::{IntrRuleAC, IntrRuleACInfo, Rule};

/// HS `dhIntruderVariantsFile` (TheoryLoader.hs:745-746, see line 746).
pub const DH_INTRUDER_VARIANTS_FILE: &str = "data/intruder_variants_dh.spthy";

/// HS `bpIntruderVariantsFile` (TheoryLoader.hs:749-750, see line 750).
pub const BP_INTRUDER_VARIANTS_FILE: &str = "data/intruder_variants_bp.spthy";

/// The DH intruder-variants spthy source, embedded at compile time
/// (HS uses `$(embedFile "data/intruder_variants_dh.spthy")` —
/// TheoryLoader.hs:753-759, see line 759).
pub const DH_INTRUDER_VARIANTS_SPTHY: &str =
    include_str!("../../../tamarin-prover/data/intruder_variants_dh.spthy");

/// The BP intruder-variants spthy source, embedded at compile time
/// (HS uses `$(embedFile "data/intruder_variants_bp.spthy")` —
/// TheoryLoader.hs:762-768, see line 768).
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
            panic!(
                "mk_dh_intruder_variants: parse error in {}: {}",
                DH_INTRUDER_VARIANTS_FILE, e
            )
        })
}

/// HS `mkBpIntruderVariants` (TheoryLoader.hs:762-768).
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
/// (HS `ctxtDesc` — Theory/Text/Parser/Rule.hs:200-204, see line 202) for human-readable
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
    let parser_rules = p::parse_intruder_rules(source).map_err(|e| IntrRuleParseError {
        ctxt_desc: ctxt_desc.to_string(),
        message: e.to_string(),
    })?;

    // Mirror HS `setState (mkStateSig msig)` — make the term-conversion
    // pass below see the 0-arity NoEq names from `msig` so bare
    // identifiers like `one` / `DH_neutral` are recognised as constants.
    let _nullary_guard = elaborate::MaudeSigNullaryGuard::set(msig);

    // HS `knownFuns = S.toList (funSyms msig)`.
    let known_funs = KnownFuns::new(msig.fun_syms.iter().copied().collect());

    let mut out = Vec::with_capacity(parser_rules.len());
    for r in parser_rules {
        let intr =
            ast_rule_to_intr_rule_ac(&known_funs, &r).map_err(|message| IntrRuleParseError {
                ctxt_desc: ctxt_desc.to_string(),
                message,
            })?;
        out.push(intr);
    }
    Ok(out)
}

/// HS `knownFuns = S.toList (funSyms msig)` together with a display-name
/// index over it, so [`KnownFuns::lookup`] is one `BTreeMap` probe rather
/// than a scan of the whole signature.  Every constructor name and every
/// `constr_name_func` segment of both cached files (126 rules) resolves
/// through it on each theory load.
struct KnownFuns {
    /// The symbols in `S.toList` order, kept for the not-found message.
    syms: Vec<FunSym>,
    /// `show_fun_sym_name` → the FIRST symbol of `syms` carrying that name.
    ///
    /// FIRST-wins is load-bearing, not an implementation detail: HS
    /// `lookupFun` is `find ((== f) . showFunSymName) knownFuns`, which
    /// returns the earliest match in `S.toList` order, and two DISTINCT
    /// symbols can share a `showFunSymName` — a user-defined AC symbol and a
    /// user-defined NoEq symbol may carry the same name, and `Ord FunSym`
    /// (FunctionSymbols.hs:150-154) orders `NoEq` before `AC`, so the NoEq
    /// one is the earlier.  An `insert` loop would let the later symbol win
    /// and silently change which `FunSym` lands in the rule info.
    by_name: std::collections::BTreeMap<std::borrow::Cow<'static, str>, FunSym>,
}

impl KnownFuns {
    /// `syms` must already be in `S.toList` order — `MaudeSig::fun_syms` is a
    /// `BTreeSet`, so iterating it is exactly that order.
    fn new(syms: Vec<FunSym>) -> KnownFuns {
        let mut by_name = std::collections::BTreeMap::new();
        for f in &syms {
            // `or_insert`, never `insert`: the first symbol carrying a name
            // is the one HS's `find` returns.
            by_name.entry(show_fun_sym_name(f)).or_insert(*f);
        }
        KnownFuns { syms, by_name }
    }

    /// HS `lookupFun` (Theory/Text/Parser/Rule.hs): resolve a plain function
    /// name against the signature's known symbols (`S.toList (funSyms msig)`)
    /// by `showFunSymName` equality.
    fn lookup(&self, f: &str) -> Result<FunSym, String> {
        self.by_name.get(f).copied().ok_or_else(|| {
            format!(
                "Failed parsing intruder rule name: no function named '{}' found in the signature (symbols: {})",
                f,
                self.syms
                    .iter()
                    .map(show_fun_sym_name)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
    }
}

/// HS `constrNameFunc` (Theory/Text/Parser/Rule.hs): recover the function
/// names encoded in a destructor rule name.  Splits on `'_'`, drops the
/// leading empty segment (the name starts with an underscore), then drops
/// the LEADING purely-numeric position segments (`supprPos` via
/// `readMaybe :: Maybe Int`); errors on an empty result.
///
/// The split is unconditional, so a function symbol whose own name contains
/// `'_'` decomposes into several segments that [`KnownFuns::lookup`] cannot resolve
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
fn ast_rule_to_intr_rule_ac(known_funs: &KnownFuns, r: &p::Rule) -> Result<IntrRuleAC, String> {
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
            let f = known_funs.lookup(cname.get(1..).unwrap_or(""))?;
            IntrRuleACInfo::ConstrRule {
                name: rest.to_vec(),
                fun: f,
            }
        }
        b'd' => {
            let dname = &r.name[1..];
            let funs = constr_name_func(dname)?
                .into_iter()
                .map(|n| known_funs.lookup(n))
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
    // The let block, restrictions, variants, and left/right fields
    // are all empty for intruder rules.  Surface them as elaboration
    // errors if present (defensive).
    if !r.let_block.is_empty() {
        return Err(format!(
            "intruder rule {} unexpectedly has a let-block",
            r.name
        ));
    }
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
            elaborate::fact_to_lnfact(f)
                .map_err(|e| format!("intruder rule {}: premise: {}", r.name, e.message))
        })
        .collect::<Result<_, _>>()?;
    let acts: Vec<LNFact> = r
        .actions
        .iter()
        .map(|f| {
            elaborate::fact_to_lnfact(f)
                .map_err(|e| format!("intruder rule {}: action: {}", r.name, e.message))
        })
        .collect::<Result<_, _>>()?;
    let concs: Vec<LNFact> = r
        .conclusions
        .iter()
        .map(|f| {
            elaborate::fact_to_lnfact(f)
                .map_err(|e| format!("intruder rule {}: conclusion: {}", r.name, e.message))
        })
        .collect::<Result<_, _>>()?;

    // HS `newVariables ps cs` — variables that appear in conclusions
    // but not premises.  The intruder-rule `.spthy` files don't have
    // any (all RHS vars are LHS vars), but compute it faithfully for
    // robustness.  HS reference: Theory.Model.Fact.newVariables
    // (lib/theory/src/Theory/Model/Fact.hs:484-494, see line 494).
    let new_vars = compute_new_vars(&prems, &concs);

    Ok(Rule::new(info, prems, concs, acts).with_new_vars(new_vars))
}

/// Mirrors HS `newVariables` (`lib/theory/src/Theory/Model/Fact.hs:484-494, see line 494`):
/// the set of variables in `conclusions` that are not in `premises`,
/// returned in deterministic order.
fn compute_new_vars(prems: &[LNFact], concs: &[LNFact]) -> Vec<tamarin_term::lterm::LNTerm> {
    use std::collections::BTreeSet;
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    fn collect(t: &tamarin_term::lterm::LNTerm, out: &mut BTreeSet<LVar>) {
        match t {
            Term::Lit(Lit::Var(v)) => {
                out.insert(*v);
            }
            Term::Lit(_) => {}
            Term::App(_, args) => {
                for a in args.iter() {
                    collect(a, out);
                }
            }
        }
    }

    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        for t in f.terms.iter() {
            collect(t, &mut prem_vars);
        }
    }
    let mut new_set: BTreeSet<LVar> = BTreeSet::new();
    for f in concs {
        for t in f.terms.iter() {
            let mut here = BTreeSet::new();
            collect(t, &mut here);
            for v in here {
                if !prem_vars.contains(&v) {
                    new_set.insert(v);
                }
            }
        }
    }
    new_set
        .into_iter()
        .map(|v| Term::Lit(Lit::Var(v)))
        .collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "intruder_variants_tests.rs"]
mod tests;
