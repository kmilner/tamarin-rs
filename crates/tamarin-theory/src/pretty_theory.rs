// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Theory pretty-printer.  Port of Haskell's `prettyClosedTheory`
//! (ClosedTheory.hs:382-418) — top-level renderer for `--prove` output.
//!
//! Goal: byte-identical output to Haskell on the analyzed theory body.
//! The output layout:
//!
//! ```text
//! theory <name>
//!
//! begin
//!
//! // Function signature and definition of the equational theory E
//!
//! builtins: ...     (if any)
//! functions: ...
//! equations: ...
//!
//! rule (modulo E) <name>:
//!    [ <prems> ] --[ <acts> ]-> [ <concs> ]
//!
//!   /* has exactly the trivial AC variant */
//!
//! restriction <name>:
//!   "<formula>"
//!
//! lemma <name> [attrs]:
//!   <quant> "<formula>"
//! /*
//! guarded formula characterizing ...:
//! "<gformula>"
//! */
//! <proof body>
//!
//! /* All wellformedness checks were successful. */ (or warning block)
//!
//! /*
//! Generated from:
//! Tamarin version ...
//! Maude version ...
//! Git revision: ...
//! Compiled at: ...
//! */
//!
//! end
//! ```
//!
//! Each top-level item is separated by a blank line (HS uses `vsep`).

use crate::pretty_formula as pf;
use crate::theory::Theory;
use tamarin_parser::ast as p;

/// Build info passed in from the prover binary so the Generated-from
/// block reflects compile-time facts.
#[derive(Debug, Clone)]
pub struct BuildInfo {
    pub tamarin_version: String,
    pub maude_version: String,
    pub git_revision: String,
    pub git_branch: String,
    pub compiled_at: String,
}

/// Per-lemma proof result produced by the prover.  When `proof_body`
/// is `None` (e.g. when the user did not pass `--prove`), the lemma's
/// stored skeleton (`by sorry`) is rendered instead.
#[derive(Debug, Clone)]
pub struct ProvedLemma {
    pub name: String,
    /// Pre-rendered HS-faithful proof body (lines of text, no leading
    /// blank line, no trailing blank line).  See `pretty_proof_body`.
    pub proof_body: Option<String>,
}

// =============================================================================
// Heuristic / GoalRanking rendering
// =============================================================================

/// Compute the default oracle name for a theory file.
///
/// Mirrors HS `defaultOracleNames` (System.hs:551-561): when an oracle
/// ranking carries no explicit relative-path, the name is derived from the
/// theory file path by the following algorithm (faithful port of the HS
/// `groupBy` computation):
///
/// 1. Take the prefix before the first `.` in `in_file`.
/// 2. Take the suffix after the last `/` in that prefix.
/// 3. Append `".oracle"`.
/// 4. If that file exists on disk → use it; otherwise → fall back to `"oracle"`.
///
/// For absolute paths the step-2 suffix starts with `/` (e.g. `/defaultoracle`),
/// so the resulting path `"/defaultoracle.oracle"` almost never exists, and the
/// function returns `"oracle"` — matching observed HS behaviour.
pub(crate) fn oracle_name_for_theory(in_file: &str) -> String {
    // Step 1: HS `head $ groupBy (\_ b -> b /= '.') srcThyInFileName`.
    // `groupBy` always keeps the first character in the head group, then
    // extends it up to (not including) the first '.' at position >= 1.  So
    // a LEADING '.' (e.g. "./foo.spthy") belongs to the prefix and is NOT a
    // terminator — the prefix is "./foo".  Mirror that by ignoring a '.' at
    // char-position 0.
    let split = in_file
        .char_indices()
        .enumerate()
        .find(|(pos, (_, ch))| *pos >= 1 && *ch == '.')
        .map(|(_, (byte, _))| byte)
        .unwrap_or(in_file.len());
    let before_dot = &in_file[..split];
    // Step 2: suffix after last '/' in before_dot.
    // HS `groupBy (\_ b -> b /= '/') s` splits `s` at every '/', then `last`
    // takes the final segment.  For absolute paths this segment starts with
    // '/' (e.g. "/defaultoracle"), so `inFileOracleName` is "/defaultoracle.oracle".
    let after_slash = match before_dot.rfind('/') {
        Some(i) => &before_dot[i..], // includes the '/' prefix, mirroring HS
        None => before_dot,
    };
    // Step 3: append ".oracle"
    let candidate = format!("{}.oracle", after_slash);
    // Step 4: existence check
    if std::path::Path::new(&candidate).exists() {
        candidate
    } else {
        "oracle".to_string()
    }
}

/// Render a single `GoalRanking` token from the raw heuristic string.
///
/// Mirrors HS `prettyGoalRanking` (System.hs:710-728):
/// - `OracleRanking`/`OracleSmartRanking` → `<char> "<oraclename>"`
/// - `InternalTacticRanking`              → `{<name>}`
/// - all others                           → single char
///
/// `oracle_name` is the already-computed default oracle name for the theory
/// (from `oracle_name_for_theory`); it is used when the ranking carries no
/// explicit name.
fn render_single_ranking(ch: char, explicit_oracle: Option<&str>, oracle_name: &str) -> String {
    match ch {
        'o' | 'O' => {
            let name = explicit_oracle.unwrap_or(oracle_name);
            format!("{} \"{}\"", ch, name)
        }
        _ => ch.to_string(),
    }
}

/// Parse a raw heuristic string and re-render it in HS style.
///
/// Mirrors `prettyGoalRankings rs = unwords (map prettyGoalRanking rs)`
/// (System.hs:706-707).  The raw string is the verbatim text stored after
/// `heuristic:` / `heuristic=` in the source file.  It may be compact
/// (`"osopo"`) or already-expanded (`"o \"oracle\" s"`).
///
/// Grammar (mirrors HS `goalRanking` in Parser/Signature.hs:308-326):
///   rankings     ::= ranking+
///   ranking      ::= oracle_ranking | tactic_ranking | letter
///   oracle_ranking ::= ('o' | 'O') ws* ('"' name '"' ws*)?
///   tactic_ranking ::= '{' [^}]* '}'
///   letter       ::= [a-zA-Z] ws*
pub fn pretty_goal_rankings(raw: &str, in_file: &str) -> String {
    let oracle_name = oracle_name_for_theory(in_file);
    let mut result = Vec::new();
    let chars: Vec<char> = raw.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // Skip comments.  HS's lexer consumes `/* … */` block and `// …`
        // line comments BETWEEN ranking tokens before parsing them, so a
        // heuristic like `p /* note for SAPIC */` parses to just `[p]`.
        // The raw string RS stores is read verbatim to end-of-line, so we
        // must skip comments here too — otherwise the comment's letters are
        // mis-tokenised as bogus rankings (and an `o` even as an oracle).
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
            i += 2;
            while i + 1 < chars.len() && !(chars[i] == '*' && chars[i + 1] == '/') {
                i += 1;
            }
            i = (i + 2).min(chars.len()); // consume closing `*/`
            continue;
        }
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            // Line comment runs to the end of the (single-line) raw string.
            break;
        }
        if c == '{' {
            // Tactic ranking: `'{' ++ _name tactic ++ "}"` (System.hs:710-728, see line 714).
            // HS's parser does `string "{" <* skipMany (char ' ')` before
            // capturing `tacticName <- many1 (noneOf "\"\n\r{}")`
            // (Parser/Signature.hs:313-315), so it STRIPS leading space(s) after `{`
            // but PRESERVES any trailing space (`noneOf` does not exclude
            // space).  Mirror that: skip leading spaces, then re-emit the rest
            // verbatim up to `}`.
            i += 1; // consume '{'
            while i < chars.len() && chars[i] == ' ' {
                i += 1;
            }
            let name_start = i;
            while i < chars.len() && chars[i] != '}' {
                i += 1;
            }
            let name: String = chars[name_start..i].iter().collect();
            if i < chars.len() {
                i += 1; // consume '}'
            }
            result.push(format!("{{{}}}", name));
        } else if c == 'o' || c == 'O' {
            i += 1;
            // Skip whitespace
            while i < chars.len() && chars[i] == ' ' {
                i += 1;
            }
            // Look for optional quoted oracle name
            if i < chars.len() && chars[i] == '"' {
                i += 1; // consume opening '"'
                let name_start = i;
                while i < chars.len() && chars[i] != '"' && chars[i] != '\n' && chars[i] != '\r' {
                    i += 1;
                }
                let explicit_name: String = chars[name_start..i].iter().collect();
                if i < chars.len() && chars[i] == '"' {
                    i += 1;
                } // consume closing '"'
                result.push(render_single_ranking(c, Some(&explicit_name), &oracle_name));
            } else {
                result.push(render_single_ranking(c, None, &oracle_name));
            }
        } else if c.is_ascii_alphabetic() {
            result.push(c.to_string());
            i += 1;
        } else {
            // Unknown character — skip
            i += 1;
        }
    }
    result.join(" ")
}

// =============================================================================

/// Render the analyzed theory in HS's `prettyClosedTheory` shape.
pub fn pretty_closed_theory(
    parsed: &p::Theory,
    elaborated: &Theory,
    proved: &[ProvedLemma],
    wf_block: &str,
    build: &BuildInfo,
    in_file: &str,
    auto_sources: bool,
) -> String {
    let mut out = String::new();

    // HS `prettyTheory` (TheoryObject.hs:741-756):
    //   vsep [ kwTheoryName name
    //        , ...configBlocks...  (filter isConfigBlock thyItems, before begin)
    //        , kwTheoryBegin, ... ]
    // ConfigBlocks: `prettyConfigBlock cb = text "configuration: " <> doubleQuotes (text cb)`
    // RS stores the configuration string directly in `parsed.configuration`.
    out.push_str("theory ");
    out.push_str(&elaborated.name);
    if let Some(cfg) = &parsed.configuration {
        // HS: `text "configuration: " <> doubleQuotes (text cb)`
        // = `configuration: "<cb>"`
        // Emitted via vsep (blank-line separated from theory name and begin).
        out.push_str("\n\nconfiguration: \"");
        out.push_str(cfg);
        out.push('"');
    }
    out.push_str("\n\nbegin\n\n");

    // // Function signature and definition of the equational theory E\n\n
    out.push_str("// Function signature and definition of the equational theory E\n\n");

    // builtins / functions / equations — render_signature already ends
    // with a trailing '\n' after each line so we don't add another here.
    out.push_str(&render_signature(&elaborated.signature.maude_sig));

    // HS `prettyTheory` (TheoryObject.hs:741-751) emits, between the
    // signature and the cache block, in this order:
    //   - `vcat $ map prettyTactic thyT` (only if non-empty tactics)
    //   - `heuristic: <ranking>` line (only if non-empty heuristic)
    //   - `ppCache` (the "looping facts with injective instances" comment).
    // `vsep` separates each non-empty element with a blank line.
    // Mirror that here.
    if !elaborated.tactic.is_empty() {
        // `vcat $ map prettyTactic thyT`: tactics joined by a single
        // newline (no blank line between them).
        let blocks: Vec<String> = elaborated.tactic.iter().map(|t| t.render()).collect();
        out.push('\n');
        out.push_str(&blocks.join("\n"));
        out.push('\n');
    }
    if !elaborated.heuristic.is_empty() {
        // HS `TheoryObject.hs:756-768, see line 764`: `text "heuristic: " <> text (prettyGoalRankings thyH)`
        // where `prettyGoalRankings = unwords . map prettyGoalRanking` (System.hs:706-707).
        // Each ranking in the Vec is a raw heuristic string; join their expansions with a
        // space.  (In practice there is only one `heuristic:` item per theory.)
        let rendered: Vec<String> = elaborated
            .heuristic
            .iter()
            .map(|raw| pretty_goal_rankings(raw, in_file))
            .collect();
        out.push('\n');
        out.push_str("heuristic: ");
        out.push_str(&rendered.join(" "));
        out.push('\n');
    }
    let inj_block = render_injective_fact_insts(elaborated);
    if !inj_block.is_empty() {
        out.push('\n');
        out.push_str(&inj_block);
        out.push('\n');
    }

    // Iterate parsed.items, mapping to elaborated entities where needed.
    // HS preserves source order via vsep over `thyItems`.  Each item is
    // separated from the previous block by a blank line.
    //
    // HS-parallel: `lib/theory/src/TheoryObject.hs:747-783, see line 759,767`
    //   `parMap rdeepseq ppItem (theoryItems thy)` (and `OpenTheory.hs:902-940, see line 914,926`).
    // HS evaluates each item's `Doc` in parallel; the final `vsep`
    // (sequential concatenation) preserves source order.  We mirror via
    // rayon `par_iter().collect()` — parallel per-item render, sequential
    // string append.
    use rayon::prelude::*;
    // Collect macros once (mirrors HS `closeProtoRule`, which applies them to
    // every rule of the closing theory, lib/theory/src/Rule.hs:82-86).
    // Computed here (not per item) so it is not re-collected and cloned for
    // every theory item.
    let macros: Vec<p::Macro> = collect_macros(parsed);
    // Names of arity-1 NoEq function symbols.  Depends only on the
    // (immutable) elaborated signature, so compute it once here and thread
    // it through to every per-item renderer rather than recomputing (and
    // re-cloning the signature) for each rule/lemma/restriction/predicate.
    let arity1 = arity1_noeq_names(elaborated);
    // HS `prettyClosedTheory` (ClosedTheory.hs:382-418, see line 383) switches the WHOLE theory
    // to the open-as-closed renderer when `containsManualRuleVariants` holds,
    // which suppresses loop-breaker comments on trivial-AC-variant rules.
    let manual_variants = contains_manual_rule_variants(parsed, elaborated, auto_sources);
    // Positional `(name, occurrence)` pairing of each parsed rule item with
    // its elaborated counterpart — see `pair_elaborated_rules`.
    let elab_rules = pair_elaborated_rules(&parsed.items, elaborated);
    let rendered: Vec<Option<String>> = parsed
        .items
        .par_iter()
        .enumerate()
        .map(|(idx, item)| {
            render_parsed_item(
                item,
                elab_rules[idx],
                &macros,
                elaborated,
                proved,
                in_file,
                &arity1,
                manual_variants,
                auto_sources,
            )
        })
        .collect();
    for b in rendered.into_iter().flatten() {
        out.push('\n');
        out.push_str(&b);
        out.push('\n');
    }

    // Wellformedness block (already preformatted: either the "all
    // successful" line or the WARNING /* ... */ block).
    out.push('\n');
    out.push_str(wf_block);
    out.push('\n');

    // Generated-from block.
    out.push('\n');
    out.push_str(&render_generated_from(build));
    out.push('\n');

    // end
    out.push_str("\nend\n");

    out
}

// =============================================================================
// Open theory (`--parse-only`) — port of HS `prettyOpenTheory`
// (OpenTheory.hs:870-877) = `prettyTheory prettySignaturePure (const emptyDoc)
// prettyOpenProtoRule prettyProof prettyTranslationElement`
// (TheoryObject.hs:747-783).  Differences from the closed print:
//   - the signature is the PARSE-time `SignaturePure` (same `prettyMaudeSig`
//     renderer — for a parsed theory the two signatures have equal content,
//     since translation has not added anything yet);
//   - `ppCache = const emptyDoc`: no "looping facts with injective instances"
//     comment and no intruder-rule section;
//   - rules render as `prettyOpenProtoRule` — the E-rule only, with NO
//     loop-breaker / AC-variant annotations (OpenTheory.hs:815-824);
//   - lemmas carry their PARSED proof skeleton (`prettyProof`), `by sorry`
//     when none was written;
//   - restrictions show no `/* expanded formula: */` block (parse-time
//     `_rstrOriginalFormula` is `Nothing` — `applyMacroInRestriction` only
//     runs at translation; oracle-verified);
//   - `TranslationItem`s render via `prettyTranslationElement`
//     (TheoryObject.hs:785-841): `builtin  <name>`, `function: …` typing
//     lines, `process:`/`let` blocks, `export:`, accountability lemmas and
//     `test` case tests;
//   - no wellformedness block and no `Generated from:` footer (Batch.hs:91-95
//     prints the doc alone).
// =============================================================================

/// Convert one parsed top-level/def process into the SAPIC `PlainProcess`
/// this module's Doc printer consumes.  Injected by the driver crate
/// (`tamarin-prover`), which owns the `tamarin-sapic` dependency —
/// `tamarin-theory` cannot depend on it (dependency direction).
pub type OpenProcessConv<'a> =
    &'a dyn Fn(&p::Process) -> Result<crate::sapic::PlainProcess, String>;

/// The `Sapic.typeTheoryEnv` output overlaid onto the open print: the typed
/// (`renameUnique` + `typeProcess`) processes replace the parse-time ones at
/// render time, keyed by occurrence order.  Produced by
/// `tamarin_sapic::type_theory::type_theory_env`; the parser AST itself stays
/// untouched (HS instead rewrites the theory's `TranslationItem`s in place,
/// `mapMProcesses`/`mapMProcessesDef`, TheoryObject.hs:279-301).
#[derive(Debug, Clone, Default)]
pub struct TypedOverlay {
    /// One typed process per process-bearing occurrence, in item order:
    /// `TopLevelProcess` and `DiffEquivLemma` contribute one each,
    /// `EquivLemma` two (first, then second) — HS `mapMProcesses`'s `f'`
    /// arms (TheoryObject.hs:279-291).
    pub processes: Vec<crate::sapic::PlainProcess>,
    /// One `(vars, body)` per `ProcessDef` item, in item order (HS
    /// `mapMProcessesDef`, TheoryObject.hs:294-301).  After typing, `vars`
    /// is always `Some` — `Some(vec![])` for a parameterless `let P = …`
    /// (Typing.hs:217-225), which renders as `let  P () =`.
    pub defs: Vec<(
        Option<Vec<crate::sapic::SapicLVar>>,
        crate::sapic::PlainProcess,
    )>,
}

/// Options for the by-module open print (`prettyOpenTheoryByModule`,
/// TheoryLoader.hs:783-801).
///
/// - `spthy`: all defaults (the plain `prettyOpenTheory`).
/// - `spthytyped`: `typed = Some(overlay)` + `extra_function_items` — the
///   overlay also DROPS every source-positioned `Functions` item
///   (`clearFunctionTypingInfos`, TheoryObject.hs:504-508), and the extra
///   items re-emit the recomputed `function:` blocks at the end
///   (Typing.hs:210 `Map.foldrWithKey addFunctionTypingInfo'` — the caller
///   passes them in DESCENDING key order).
/// - `msr`: `drop_translation_items = true` — every `TranslationElement`
///   analogue renders empty (`prettyOpenTranslatedTheory` after
///   `removeTranslationItems`, OpenTheory.hs:47-52, 891-898).
#[derive(Debug, Clone, Default)]
pub struct OpenPrintOpts {
    pub typed: Option<TypedOverlay>,
    /// Recomputed `function:` typing items appended after the source items
    /// (before the wellformedness / version comment blocks).
    pub extra_function_items: Vec<crate::theory::SapicFunSym>,
    /// Zero out the `TranslationElement` set: `Builtins`, `Functions`,
    /// `TopLevelProcess`, `ProcessDef`, `EquivLemma`, `DiffEquivLemma`,
    /// `Export`, `AccLemma`, `CaseTest` (Items/TheoryItem.hs:43-53).
    pub drop_translation_items: bool,
}

/// Pretty-print the parsed open theory — HS `prettyOpenTheory` as emitted by
/// `--parse-only` (Batch.hs:91-95 `putStrLn . renderDoc`; the returned string
/// carries NO trailing newline, the caller's `println!` supplies `putStrLn`'s).
///
/// `elaborated` supplies the parse-time signature (`prettySignaturePure`
/// content), the hoisted `heuristic:`/`tactic:` headers, and the arity-1
/// symbol set for the parse-time `naryOpApp` fold; the elaborated RULES are
/// never consulted (open rules render from the parser AST alone).
pub fn pretty_open_theory(
    parsed: &p::Theory,
    elaborated: &Theory,
    in_file: &str,
    conv: OpenProcessConv<'_>,
) -> Result<String, String> {
    let mut blocks =
        open_theory_blocks(parsed, elaborated, in_file, conv, &OpenPrintOpts::default())?;
    blocks.push("end".to_string());
    Ok(blocks.join("\n\n"))
}

/// The by-module open print — HS `prettyOpenTheoryByModule`'s
/// `spthy`/`spthytyped`/`msr` arms (TheoryLoader.hs:783-801) followed by the
/// two trailing comment `TextItem`s `withVersionAndReport` appends
/// (TheoryLoader.hs:636-660): the wellformedness block (`reportToDoc` — pass
/// the pre-rendered [`format_wf_block`] string) and the `Generated from:`
/// version block.  Which theory shape gets rendered is entirely in `opts`
/// (see [`OpenPrintOpts`]); the returned string carries NO trailing newline
/// (`putStrLn`'s caller supplies it, and `-o FILE` writes it verbatim).
pub fn pretty_open_theory_by_module(
    parsed: &p::Theory,
    elaborated: &Theory,
    in_file: &str,
    conv: OpenProcessConv<'_>,
    opts: &OpenPrintOpts,
    wf_block: &str,
    build: &BuildInfo,
) -> Result<String, String> {
    let mut blocks = open_theory_blocks(parsed, elaborated, in_file, conv, opts)?;
    blocks.push(wf_block.to_string());
    blocks.push(render_generated_from(build));
    blocks.push("end".to_string());
    Ok(blocks.join("\n\n"))
}

/// Shared block list of the open print: everything from `theory <name>` up to
/// (but not including) the final `end`, one `vsep` block per entry.
fn open_theory_blocks(
    parsed: &p::Theory,
    elaborated: &Theory,
    in_file: &str,
    conv: OpenProcessConv<'_>,
    opts: &OpenPrintOpts,
) -> Result<Vec<String>, String> {
    // HS `prettyTheory` (TheoryObject.hs:757-770) = `vsep` over:
    //   [ kwTheoryName, configBlocks…, kwTheoryBegin, lineComment_ "…",
    //     ppSig, tactics?, heuristic?, ppCache ] ++ items ++ [kwEnd].
    // `vsep = foldr ($--$) emptyDoc` skips empty docs and separates the
    // non-empty blocks with exactly one blank line — modelled here as a
    // Vec<String> of newline-free-trailing blocks joined with "\n\n".
    let mut blocks: Vec<String> = Vec::new();
    blocks.push(format!("theory {}", parsed.name));
    if let Some(cfg) = &parsed.configuration {
        // `prettyConfigBlock cb = text "configuration: " <> doubleQuotes (text cb)`
        // (TheoryObject.hs:921-922), filtered BEFORE `begin` (line 760).
        blocks.push(format!("configuration: \"{}\"", cfg));
    }
    blocks.push("begin".to_string());
    blocks.push("// Function signature and definition of the equational theory E".to_string());
    // `prettySignaturePure = prettyMaudeSig . sigpMaudeSig`
    // (Theory/Model/Signature.hs:173-175)
    // — the same three-line `builtins:/functions:/equations:` vcat the closed
    // print emits (`render_signature`), whose sub-blocks are single-newline
    // separated; strip the trailing '\n' so the block joins via the vsep glue.
    let sig_block = render_signature(&elaborated.signature.maude_sig);
    let sig_trimmed = sig_block.trim_end_matches('\n');
    if !sig_trimmed.is_empty() {
        blocks.push(sig_trimmed.to_string());
    }
    // `vcat $ map prettyTactic thyT` (TheoryObject.hs:764) — single-newline
    // joined tactic blocks; then the `heuristic:` line (line 765).  Both are
    // hoisted header fields in HS (never item-positioned), which `elaborate`
    // mirrors by collecting the parser's Tactic/Heuristic items.
    if !elaborated.tactic.is_empty() {
        let tblocks: Vec<String> = elaborated.tactic.iter().map(|t| t.render()).collect();
        blocks.push(tblocks.join("\n"));
    }
    if !elaborated.heuristic.is_empty() {
        let rendered: Vec<String> = elaborated
            .heuristic
            .iter()
            .map(|raw| pretty_goal_rankings(raw, in_file))
            .collect();
        blocks.push(format!("heuristic: {}", rendered.join(" ")));
    }
    // `ppCache = const emptyDoc` (OpenTheory.hs:872) — nothing here.

    // Per-item blocks, source order (`parMap rdeepseq ppItem (thyItems thy)`,
    // TheoryObject.hs:767 — parallel render, sequential vsep order).
    let predicates: Vec<p::Predicate> = collect_predicates(parsed);
    let arity1 = arity1_noeq_names(elaborated);
    let mut st = OpenPrintState {
        opts,
        proc_idx: 0,
        def_idx: 0,
    };
    for item in &parsed.items {
        blocks.extend(render_open_item(
            item,
            &predicates,
            in_file,
            &arity1,
            &elaborated.signature.maude_sig,
            conv,
            &mut st,
        )?);
    }
    // Recomputed `function:` items land at the END of `thyItems`
    // (`addFunctionTypingInfo` appends, TheoryObject.hs:492-493) — i.e. after
    // every source item, before the wf/version comments the caller appends.
    for fti in &opts.extra_function_items {
        blocks.push(pretty_function_typing_info(fti).render());
    }
    Ok(blocks)
}

/// The print options plus the two overlay cursors threaded through the
/// per-item render: HS consumes the typed processes / process-defs by
/// occurrence order (`mapMProcesses` / `mapMProcessesDef`,
/// TheoryObject.hs:279-301), so each `TypedOverlay` slot is taken exactly
/// once as the item list is walked.
struct OpenPrintState<'a> {
    opts: &'a OpenPrintOpts,
    /// Next unconsumed [`TypedOverlay::processes`] index.
    proc_idx: usize,
    /// Next unconsumed [`TypedOverlay::defs`] index.
    def_idx: usize,
}

/// One parsed theory item → its open-print blocks (usually 0 or 1; a
/// `builtins:`/`functions:`/`predicates:` line yields one block PER declared
/// entry, since HS appends one `TheoryItem` per entry — Parser/Signature.hs:97
/// (`SignatureBuiltin`), TheoryObject.hs:492-493 (`FunctionTypingInfo`),
/// TheoryObject.hs:540-543 (`PredicateItem`)).
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_open_item(
    item: &p::TheoryItem,
    predicates: &[p::Predicate],
    in_file: &str,
    arity1: &std::collections::HashSet<String>,
    msig: &tamarin_term::maude_sig::MaudeSig,
    conv: OpenProcessConv<'_>,
    st: &mut OpenPrintState<'_>,
) -> Result<Vec<String>, String> {
    use crate::pretty_hpj::Doc;
    use p::TheoryItem::*;
    let opts = st.opts;
    // `msr`: `removeTranslationItems` maps every `TranslationItem _` to
    // `TranslationItem ()` (OpenTheory.hs:47-52) and
    // `prettyOpenTranslatedTheory` renders those as `emptyDoc`
    // (OpenTheory.hs:891-899 with `emptyString`), so the whole
    // `TranslationElement` set (Items/TheoryItem.hs:43-53) vanishes.
    if opts.drop_translation_items {
        if let Builtins(_)
        | Functions(_)
        | TopLevelProcess(_)
        | ProcessDef(_)
        | EquivLemma(..)
        | DiffEquivLemma(_)
        | Export { .. }
        | AccLemma(_)
        | CaseTest(_) = item
        {
            return Ok(Vec::new());
        }
    }
    // `spthytyped`: substitute the typed processes/defs by occurrence order
    // and drop the source-positioned `function:` items
    // (`clearFunctionTypingInfos`; the recomputed set is re-appended at the
    // end by `open_theory_blocks`).
    if let Some(overlay) = &opts.typed {
        let take_proc = |idx: &mut usize| -> Result<&crate::sapic::PlainProcess, String> {
            let p = overlay
                .processes
                .get(*idx)
                .ok_or_else(|| "typed overlay: process count mismatch".to_string())?;
            *idx += 1;
            Ok(p)
        };
        match item {
            Functions(_) => return Ok(Vec::new()),
            TopLevelProcess(_) => {
                let pp = take_proc(&mut st.proc_idx)?;
                return Ok(vec![Doc::text("process:")
                    .above_g(open_process_doc(pp).nest(2))
                    .render()]);
            }
            EquivLemma(_, _) => {
                let d1 = take_proc(&mut st.proc_idx)?;
                let d2 = take_proc(&mut st.proc_idx)?;
                return Ok(vec![Doc::text("equivLemma:")
                    .above_g(open_process_doc(d1).nest(2))
                    .above(open_process_doc(d2).nest(2))
                    .render()]);
            }
            DiffEquivLemma(_) => {
                let d = take_proc(&mut st.proc_idx)?;
                return Ok(vec![Doc::text("diffEquivLemma:")
                    .above_g(open_process_doc(d).nest(2))
                    .render()]);
            }
            ProcessDef(pd) => {
                let (vars, body) = overlay
                    .defs
                    .get(st.def_idx)
                    .ok_or_else(|| "typed overlay: process-def count mismatch".to_string())?;
                st.def_idx += 1;
                let mut d = Doc::text("let ").beside_sp(Doc::text(pd.name.clone()));
                if let Some(vs) = vars {
                    // `map show l` over typed `SapicLVar`s
                    // (Theory/Sapic/Term.hs:108-110): LVar display plus
                    // `:type` suffix.
                    let shown: Vec<String> = vs
                        .iter()
                        .map(crate::pretty_sapic::show_sapic_lvar)
                        .collect();
                    d = d.beside_sp(Doc::text(format!("({})", shown.join(","))));
                }
                d = d
                    .beside_sp(Doc::text("="))
                    .beside_sp(open_process_doc(body).nest(2));
                return Ok(vec![d.render()]);
            }
            _ => {}
        }
    }
    Ok(match item {
        // Every `builtins:` entry appends `TranslationItem (SignatureBuiltin
        // name)` (Parser/Signature.hs:89-101, see line 97), rendered
        // `text "builtin " <-> text s` (TheoryObject.hs:843) = two spaces.
        Builtins(names) => names.iter().map(|n| format!("builtin  {}", n)).collect(),
        // Every `functions:` declaration appends `FunctionTypingInfo`
        // (Theory/Text/Parser.hs:259-262, TheoryObject.hs:492-493), rendered by the two
        // `prettyTranslationElement` typing cases (TheoryObject.hs:800-838).
        Functions(decls) => decls
            .iter()
            .map(|d| pretty_function_typing_info(&function_decl_typing_info(d)).render())
            .collect(),
        // `equations:` / `options:` only mutate the signature/options — no
        // theory item (Parser/Signature.hs:232-249, 252-269).  `heuristic:` /
        // `tactic:` land in the hoisted header fields (rendered above).
        // `#define`/`#include` are parse-time preprocessing.  `rule (modulo
        // AC)` intruder rules go to `thyCache`, which the open print's
        // `ppCache = const emptyDoc` drops.  Diff-mode lemmas are
        // unreachable (the driver rejects `--diff` earlier).
        Equations { .. }
        | Options(_)
        | Heuristic(_)
        | Tactic(_)
        | Define(_)
        | Include(_)
        | IntrRule(_)
        | DiffLemma(_) => Vec::new(),
        Rule(r) => vec![render_open_rule(r, arity1)],
        Lemma(l) => vec![render_open_lemma(l, predicates, in_file, arity1, msig)],
        // `axiom` is the deprecated synonym parsed into a `RestrictionItem`
        // (`legacyAxiom` → `liftedAddRestriction`, Theory/Text/Parser.hs:270-272).
        Restriction(r) | LegacyAxiom(r) => {
            vec![render_open_restriction(r, predicates, arity1, msig)]
        }
        Predicates(preds) => preds
            .iter()
            .map(|pr| render_predicate(pr, arity1))
            .collect(),
        Macros(ms) => {
            if ms.is_empty() {
                Vec::new()
            } else {
                vec![render_parsed_macros(ms)]
            }
        }
        FormalComment { header, body } => {
            // Same shape as the closed print (`prettyFormalComment`,
            // lib/theory/src/Pretty.hs:19-21).
            if header.is_empty() {
                vec![format!("/*\n{}\n*/", body)]
            } else {
                vec![format!("{}{{*{}*}}", header, body)]
            }
        }
        // `prettyTranslationElement (ProcessItem p)` (TheoryObject.hs:786):
        //   `text "process" <> colon $-$ (nest 2 $ prettyProcess p)`.
        TopLevelProcess(proc) => {
            let pp = conv(proc)?;
            vec![Doc::text("process:")
                .above_g(open_process_doc(&pp).nest(2))
                .render()]
        }
        // `prettyTranslationElement (ProcessDefItem p)` (TheoryObject.hs:791-799):
        //   `text "let " <-> name <-> vars? <-> text "=" <-> nest 2 (prettyProcess body)`
        // — note `text "let "` keeps its own trailing space, so `<->` yields
        // the oracle's `let  P …` double space.
        ProcessDef(pd) => {
            let body = conv(&pd.body)?;
            let mut d = Doc::text("let ").beside_sp(Doc::text(pd.name.clone()));
            if let Some(vs) = &pd.vars {
                // `text ("(" ++ intercalate "," (map show l) ++ ")")` — `show`
                // on a `SapicLVar` is the LVar display (sort sigil + name,
                // `.idx` only when non-zero — always 0 at parse) plus an
                // optional `:type` suffix (Theory/Sapic/Term.hs:108-110).
                let shown: Vec<String> = vs.iter().map(show_open_varspec).collect();
                d = d.beside_sp(Doc::text(format!("({})", shown.join(","))));
            }
            d = d
                .beside_sp(Doc::text("="))
                .beside_sp(open_process_doc(&body).nest(2));
            vec![d.render()]
        }
        // `prettyTranslationElement (EquivLemma p1 p2)` (TheoryObject.hs:788):
        //   `text "equivLemma" <> colon $-$ (nest 2 p1) $$ (nest 2 p2)`.
        EquivLemma(p1, p2) => {
            let d1 = conv(p1)?;
            let d2 = conv(p2)?;
            vec![Doc::text("equivLemma:")
                .above_g(open_process_doc(&d1).nest(2))
                .above(open_process_doc(&d2).nest(2))
                .render()]
        }
        // `prettyTranslationElement (DiffEquivLemma p)` (TheoryObject.hs:787).
        DiffEquivLemma(proc) => {
            let d = conv(proc)?;
            vec![Doc::text("diffEquivLemma:")
                .above_g(open_process_doc(&d).nest(2))
                .render()]
        }
        // `prettyTranslationElement (ExportInfoItem eInfo)` (TheoryObject.hs:
        // 839-842): `text "export: " <-> tag <-> nest 2 (doubleQuotes body)`
        // — all flat text chunks, so the layout is a plain concatenation with
        // `<->`'s single spaces (`export:  tag "body"`, double space after the
        // colon from `"export: "`'s own trailing space).  The body is emitted
        // verbatim (embedded newlines stay at column 0 — HughesPJ cannot
        // re-indent inside one `text` chunk).  HS's opening `symbol "\""`
        // lexeme skips the whitespace right after the quote
        // (Parser/Signature.hs:287-295), which the RS lexer keeps — trim it.
        Export { tag, body } => {
            vec![format!("export:  {} \"{}\"", tag, body.trim_start())]
        }
        // `prettyAccLemma` (Items/AccLemmaItem.hs:47-57):
        //   kwLemma <-> name[attrs] <> colon $-$ nest 2 (
        //     text (intercalate ", " caseIdents) <-> "accounts for" $-$
        //     sep [doubleQuotes (prettySyntacticLNFormula aFormula)])
        // The formula is the PARSED one (no macro/predicate expansion —
        // accountability lemmas skip `expandLemma`, Theory/Text/Parser.hs:276-279).
        AccLemma(al) => {
            use crate::pretty_hpj as hpj;
            let kw = Doc::text("lemma");
            let name_doc = Doc::text(al.name.clone());
            let header = if al.attributes.is_empty() {
                kw.beside_sp(name_doc).beside(Doc::text(":"))
            } else {
                let attr_docs: Vec<Doc> = lemma_attr_docs(&al.attributes, in_file);
                let attrs_fsep = hpj::fsep(hpj::punctuate(Doc::text(","), attr_docs));
                let brackets = Doc::text("[").beside(attrs_fsep).beside(Doc::text("]"));
                kw.beside_sp(name_doc)
                    .beside_sp(brackets)
                    .beside(Doc::text(":"))
            };
            let f = crate::elaborate::canonicalize_ac_in_formula(
                &crate::elaborate::rewrite_arity1_formula(&al.formula, arity1),
            );
            let mut out = header.render();
            out.push_str("\n  ");
            out.push_str(&al.case_test_idents.join(", "));
            out.push_str(" accounts for\n");
            out.push_str(&pf::formula_doublequoted_nested(&f, 2));
            vec![out]
        }
        // `prettyCaseTest` (Items/CaseTestItem.hs:39-45):
        //   text "test" <-> name <> colon $-$ nest 2 (sep [doubleQuotes f]).
        CaseTest(ct) => {
            let f = crate::elaborate::canonicalize_ac_in_formula(
                &crate::elaborate::rewrite_arity1_formula(&ct.formula, arity1),
            );
            vec![format!(
                "test {}:\n{}",
                ct.name,
                pf::formula_doublequoted_nested(&f, 2)
            )]
        }
    })
}

/// Build the `SapicFunSym` a `functions:` declaration records as its
/// `FunctionTypingInfo` item (HS `function`, Parser/Signature.hs:185-233:
/// the parsed name/arity/attribute flags plus the declared SAPIC types).
fn function_decl_typing_info(d: &p::FunctionDecl) -> crate::theory::SapicFunSym {
    use tamarin_term::function_symbols::{
        AcFctSym, Constructability, NdcState, NoEqSym, Privacy, UserDefinedSym,
    };
    let privacy = if d.private {
        Privacy::Private
    } else {
        Privacy::Public
    };
    let constructability = if d.destructor {
        Constructability::Destructor
    } else {
        Constructability::Constructor
    };
    // `joinNDC` (Parser/Signature.hs:196-198).
    let ndc = match (d.ndc, d.ndc_diff) {
        (false, false) => NdcState::NotNdc,
        (true, false) => NdcState::IsNdc,
        (false, true) => NdcState::IsNdcDiff,
        (true, true) => NdcState::IsNdcBoth,
    };
    let sym = if d.ac {
        UserDefinedSym::AcFctUser(AcFctSym::new(
            d.name.as_bytes().to_vec(),
            privacy,
            constructability,
            ndc,
        ))
    } else {
        UserDefinedSym::NoEqUser(
            NoEqSym::new(
                d.name.as_bytes().to_vec(),
                d.arg_types.len(),
                privacy,
                constructability,
            )
            .with_ndc(ndc),
        )
    };
    crate::theory::SapicFunSym {
        sym,
        arg_types: d.arg_types.clone(),
        out_type: d.out_type.clone(),
    }
}

/// `show` on a parse-time process-def formal (HS `Show SapicLVar`,
/// Theory/Sapic/Term.hs:108-110): the LVar display (sigil + name, `.idx`
/// when non-zero) plus `:type` when annotated.
fn show_open_varspec(v: &p::VarSpec) -> String {
    let mut s = tamarin_term::lterm::sort_prefix(v.sort).to_string();
    s.push_str(&v.name);
    if v.idx != 0 {
        s.push('.');
        s.push_str(&v.idx.to_string());
    }
    if let Some(t) = &v.typ {
        s.push(':');
        s.push_str(t);
    }
    s
}

/// HS `prettyOpenProtoRule` (OpenTheory.hs:815-824): the E-rule alone for the
/// (universal) empty-variants case; a rule that carries a manual
/// `variants (modulo AC)` block appends it via
/// `nest 1 (kwVariants $-$ nest 1 (ppList prettyProtoRuleAC variants))`.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_open_rule(parsed_rule: &p::Rule, arity1: &std::collections::HashSet<String>) -> String {
    let (mut out, _, _, _) = render_rule_e_block(parsed_rule, arity1);
    if !parsed_rule.variants.is_empty() {
        // Manual in-rule variants (`protoRule`'s `symbol "variants" *>
        // commaSep1 protoRuleAC`, Parser/Rule.hs:130-135).  Absent from the
        // example corpus outside comments; rendered best-effort in the HS
        // shape (`nest 1 (kwVariants $-$ nest 1 (ppList prettyProtoRuleAC
        // variants))`, OpenTheory.hs:818-824: each variant as its
        // `rule (modulo AC)` header + body, the list `,`-separated).
        out.push_str("\n variants (modulo AC)");
        for (i, v) in parsed_rule.variants.iter().enumerate() {
            if i > 0 {
                out.push_str("\n  ,");
            }
            let (vblock, _, _, _) = render_rule_e_block(v, arity1);
            let vblock = vblock.replacen("rule (modulo E)", "rule (modulo AC)", 1);
            for line in vblock.lines() {
                out.push_str("\n  ");
                out.push_str(line);
            }
        }
    }
    out
}

/// Open-print lemma (HS `prettyLemma prettyProof` inside `prettyOpenTheory`):
/// the shared head over the parse-time `_lFormula` plus the PARSED proof
/// skeleton (`by sorry` when none).
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_open_lemma(
    lem: &p::Lemma,
    predicates: &[p::Predicate],
    in_file: &str,
    arity1: &std::collections::HashSet<String>,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> String {
    // HS `expandLemma` (TheoryObject.hs:439-446) predicate-expands the lemma
    // formula at parse; the term parser folds surplus args of arity-1
    // functions into a pair (`naryOpApp` `k == 1`, Parser/Term.hs:94-96) —
    // e.g. `h(H, x)` → `h(<H, x>)` — and `fAppAC` sorts AC arguments when the
    // `LNTerm` is built (Term/Term/Raw.hs:118-122), where the parser AST keeps
    // written order.  The fold runs BEFORE the AC sort so the canonicaliser
    // sees the folded `h(<…>)` shape.
    let header_formula =
        crate::elaborate::canonicalize_ac_in_formula(&crate::elaborate::rewrite_arity1_formula(
            &expand_predicates_for_display(&lem.formula, predicates),
            arity1,
        ));
    let mut out = render_lemma_head(
        lem,
        in_file,
        pf::formula_doc(&header_formula),
        &render_open_guarded_block(lem, predicates, arity1, msig),
    );
    out.push('\n');
    match lem.proof.as_ref().and_then(|ps| ps.tree.as_ref()) {
        Some(tree) => {
            let mut body = String::new();
            pp_open_proof(tree, &mut body, 0, msig);
            out.push_str(&body);
        }
        None => out.push_str("by sorry"),
    }
    out
}

/// Open-print restriction — HS `prettyRestriction` (TheoryObject.hs:889-901)
/// on the PARSE-time `Restriction`: `_rstrOriginalFormula` is still `Nothing`
/// (only translation's `applyMacroInRestriction` fills it), so the top formula
/// is the parse-time `_rstrFormula` (predicate-expanded by
/// `liftedExpandRestriction` at parse, macro calls intact), the safety check
/// runs on that same formula, and the `case ogFormula of Just _ →
/// /* expanded formula: */` block is skipped.  Oracle-verified: `--parse-only`
/// prints a macro-using restriction without the expanded block.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_open_restriction(
    r: &p::Restriction,
    predicates: &[p::Predicate],
    arity1: &std::collections::HashSet<String>,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> String {
    let original =
        crate::elaborate::canonicalize_ac_in_formula(&crate::elaborate::rewrite_arity1_formula(
            &expand_predicates_for_display(&r.formula, predicates),
            arity1,
        ));
    use crate::pretty_hpj::{keyword_, line_comment_};
    let mut out = String::new();

    out.push_str(&keyword_("restriction").render());
    out.push(' ');
    out.push_str(&r.name);
    render_restriction_attributes(&r.attributes, &mut out);
    out.push_str(":\n");
    out.push_str(&pf::formula_doublequoted_nested(&original, 2));
    if is_safety_formula_parsed(&original, msig) {
        out.push_str("\n  ");
        out.push_str(&line_comment_("safety formula").render());
    }
    out
}

/// HS `prettySapic'` (Theory/Sapic/Process.hs:485-502) as a Doc:
///
/// ```haskell
/// prettySapic' ppRR p
///     | (ProcessNull _) <- p = text "0"
///     | (ProcessComb c _ pl pr) <- p = r pl <-> text (prettySapicComb c) <-> r pr
///     | (ProcessAction Rep _ p') <- p = ppAct Rep <> parens (r p')
///     | (ProcessAction a@ProcessCall {} _ _ ) <- p = ppAct a
///     | (ProcessAction a _ (ProcessNull _)) <- p = ppAct a
///     | (ProcessAction a _ p'@ProcessComb {}) <- p = ppAct a <> semi $-$ nest 1 (parens (r p'))
///     | (ProcessAction a _ p') <- p = ppAct a <> semi $-$ r p'
/// ```
///
/// The action/combinator TEXT comes from [`crate::pretty_sapic::pretty_sapic_top_level`]
/// (the byte-faithful `prettySapicTopLevel'` port, which appends `";"` to a
/// non-`!` action — stripped here, since `prettySapic'` adds `semi` itself
/// only on the continuation cases).  This reproduces upstream's layout
/// verbatim, including the surprising `then-branch if-cond else-branch`
/// operand order of `ProcessComb` (oracle-verified).
///
/// `prettyProcess = prettySapic = prettySapic' rulePrinter`
/// (TheoryObject.hs:851-852, Print.hs:52-53), so an embedded MSR renders its
/// premises through `unextractMatchingVariables mv` — every pattern-match
/// variable keeps its `=` marker.  This is the printer that
/// [`crate::pretty_sapic::pretty_sapic_top_level`] selects; the
/// `process="..."` rule attribute uses the other one.
fn open_process_doc(pr: &crate::sapic::PlainProcess) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{parens, Doc};
    use crate::sapic::{Process, SapicAction};
    // `prettySapicTopLevel'` text for this node, without the trailing `;` it
    // appends to non-`!` actions (no action string otherwise ends in ';').
    let node_text = |p: &crate::sapic::PlainProcess| -> String {
        let s = crate::pretty_sapic::pretty_sapic_top_level(p);
        s.strip_suffix(';').map(str::to_string).unwrap_or(s)
    };
    match pr {
        Process::Null(_) => Doc::text("0"),
        Process::Comb(_, _, pl, pr2) => open_process_doc(pl)
            .beside_sp(Doc::text(node_text(pr)))
            .beside_sp(open_process_doc(pr2)),
        Process::Action(SapicAction::Rep, _, p2) => {
            Doc::text("!").beside(parens(open_process_doc(p2)))
        }
        // A `ProcessCall`'s continuation is NEVER printed (Theory/Sapic/Process.hs:496).
        Process::Action(SapicAction::ProcessCall(_, _), _, _) => Doc::text(node_text(pr)),
        Process::Action(_, _, p2) => match p2.as_ref() {
            Process::Null(_) => Doc::text(node_text(pr)),
            Process::Comb(_, _, _, _) => Doc::text(format!("{};", node_text(pr)))
                .above_g(parens(open_process_doc(p2)).nest(1)),
            _ => Doc::text(format!("{};", node_text(pr))).above_g(open_process_doc(p2)),
        },
    }
}

/// The parsed proof-method Doc for the open skeleton echo — HS
/// `prettyProofMethod` (ProofMethod.hs:1173-1187) over the methods the proof
/// PARSER can produce (Parser/Proof.hs:75-85: reasons are always `Nothing`,
/// so `sorry`/`contradiction` never carry comments).
fn open_method_doc(
    m: &tamarin_parser::ast::ParsedMethod,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{keyword_, line_comment_, Doc};
    use tamarin_parser::ast::ParsedMethod as PM;
    match m {
        PM::Sorry => keyword_("sorry"),
        PM::Contradiction => keyword_("contradiction"),
        PM::Simplify => keyword_("simplify"),
        PM::Induction => keyword_("induction"),
        // Re-render the stored goal text through the same structured-goal
        // builders the live path uses (HS keeps `SolveGoal goal` structured
        // and re-prints via `prettyGoal`, so stored layout must not be echoed
        // verbatim — see `raw_solve_to_doc`).
        PM::SolveGoal(_, raw) => raw_solve_to_doc(raw, msig),
        PM::SolvedLeaf => keyword_("SOLVED").beside_sp(line_comment_("trace found")),
        PM::Unfinishable => {
            keyword_("UNFINISHABLE").beside_sp(line_comment_("reducible operator in subterm"))
        }
        PM::Invalidated => line_comment_(
            "proof may have been invalidated by editing a reuse lemma above. You should ",
        ),
        // Unrecognised method tokens: echo the captured text (parser
        // fall-through; not produced for well-formed proofs).
        PM::Other(s) => Doc::text(s.clone()),
    }
}

/// Echo a PARSED proof skeleton — HS `prettyProof = prettyProofWith
/// (prettyProofMethod . psMethod) (const id)` (Theory/Proof.hs:1051-1075).
/// Same case/next/qed assembly as the closed `pp_proof`, over the parsed
/// tree.  Cases were stored via `M.fromList` (Parser/Proof.hs:112), so they
/// echo in SORTED name order regardless of source order (oracle-verified).
fn pp_open_proof(
    tree: &tamarin_parser::ast::ParsedProofTree,
    out: &mut String,
    depth: usize,
    msig: &tamarin_term::maude_sig::MaudeSig,
) {
    use tamarin_parser::ast::ParsedMethod as PM;
    let base = depth * 2;
    let mut cases: Vec<&(String, tamarin_parser::ast::ParsedProofTree)> =
        tree.cases.iter().collect();
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    match cases.as_slice() {
        // `ppCases ps@(ProofStep (Finished Solved) _) [] = prettyStep ps`
        // (Theory/Proof.hs:1064) — no `by ` prefix on the SOLVED leaf.
        [] if matches!(tree.method, PM::SolvedLeaf) => {
            out.push_str(&pf::step_line_with_unann(
                open_method_doc(&tree.method, msig),
                base,
                true,
                "",
            ));
        }
        // `ppCases ps [] = prettyCase ps (kwBy <> text " ") <> prettyStep ps`.
        [] => {
            out.push_str(&pf::step_line_with_unann(
                open_method_doc(&tree.method, msig),
                base,
                true,
                "by ",
            ));
        }
        // `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf`.
        [(label, child)] if label.is_empty() => {
            out.push_str(&pf::step_line_with_unann(
                open_method_doc(&tree.method, msig),
                base,
                true,
                "",
            ));
            out.push('\n');
            out.push_str(&"  ".repeat(depth));
            pp_open_proof(child, out, depth, msig);
        }
        multi => {
            out.push_str(&pf::step_line_with_unann(
                open_method_doc(&tree.method, msig),
                base,
                true,
                "",
            ));
            for (i, (name, child)) in multi.iter().enumerate() {
                if i > 0 {
                    out.push('\n');
                    out.push_str(&"  ".repeat(depth));
                    out.push_str("next");
                }
                out.push('\n');
                let pad = "  ".repeat(depth + 1);
                out.push_str(&pad);
                out.push_str("case ");
                out.push_str(name);
                out.push('\n');
                out.push_str(&pad);
                pp_open_proof(child, out, depth + 1, msig);
            }
            out.push('\n');
            out.push_str(&"  ".repeat(depth));
            out.push_str("qed");
        }
    }
}

// =============================================================================
// Interactive-web snippet reuse (Web/Theory.hs `messageSnippet` /
// `rulesSnippet` / `htmlSource`).  These re-expose the byte-faithful
// `--prove` printers so the web handler (`tamarin-server`) renders the same
// text the CLI does — the web handler only adds the surrounding HTML tags.
// =============================================================================

/// HS `prettySignatureWithMaude sig = prettyMaudeSig (mhMaudeSig …)`
/// (Signature.hs) — the same signature block the theory body prints
/// (`render_signature`).  Used by the web message page's "Signature" section.
pub fn web_signature_block(sig: &tamarin_term::maude_sig::MaudeSig) -> String {
    // `render_signature` appends a trailing `\n` after each block for the
    // `--prove` theory-body layout (where more theory items follow).  HS's
    // `prettySignatureWithMaude` is one self-contained Doc with no trailing
    // blank, and `messageSnippet` wraps just that Doc: strip the trailing
    // newline so `</p>` glues directly after the last signature line.
    render_signature(sig).trim_end_matches('\n').to_string()
}

/// HS `ppPrem = nest 2 (doubleQuotes (prettyGoal th._cdGoal))`
/// (Web/Theory.hs:820-845, see line 830).  `doubleQuotes d = char '"' <> d <> char '"'` (the
/// quotes entity-escape to `&quot;` under the active HtmlDoc guard); the
/// `nest 2` indents wrapped continuation lines.  Rendered as ONE Doc so a long
/// source goal wraps exactly as HS `renderHtmlDoc` (the per-case `<p>` prem).
fn web_source_prem_doc(g: &crate::constraint::constraints::Goal) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    Doc::text("\"")
        .beside(solve_goal_to_doc(g))
        .beside(Doc::text("\""))
        .nest(2)
}

/// HS per-case `withTag "p" [] ppPrem` premise (Web/Theory.hs:820-845, see line 837): the whole
/// `<p>` is built as ONE Doc via `with_tag`, so the `nest 2` indents only
/// WRAPPED continuation lines — the `<p>` tag is zero-width and the prem sits
/// BESIDE it, so line 1 carries no leading indent (a standalone `.render()`
/// WOULD emit the nest on line 1, which HS does not).  Returns `<p>…</p>`.
pub fn web_pretty_source_prem(g: &crate::constraint::constraints::Goal) -> String {
    crate::pretty_hpj::with_tag("p", &[], web_source_prem_doc(g)).render()
}

/// HS `ppHeader = hsep [text "Sources of" <-> ppPrem, parens (nCases <->
/// text "cases")]` (Web/Theory.hs:832-834).  Built and rendered as ONE Doc so
/// the goal wraps at the web width WITH the `Sources of ` prefix offset — the
/// `<h2>` source header (`n_cases` is the number of cases).
pub fn web_pretty_source_header(
    g: &crate::constraint::constraints::Goal,
    n_cases: usize,
) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    let left = Doc::text("Sources of").beside_sp(web_source_prem_doc(g));
    let right = hpj::parens(Doc::text(n_cases.to_string()).beside_sp(Doc::text("cases")));
    hpj::hsep(vec![left, right]).render()
}

/// Collect the theory's macro declarations in source order (mirrors HS
/// `applyMacroInRestriction` / `parseLemmaWithMacros`).
pub(crate) fn collect_macros(parsed: &p::Theory) -> Vec<p::Macro> {
    parsed
        .items
        .iter()
        .filter_map(|i| {
            if let p::TheoryItem::Macros(ms) = i {
                Some(ms.as_slice())
            } else {
                None
            }
        })
        .flatten()
        .cloned()
        .collect()
}

/// Collect the theory's predicate declarations in source order.
pub(crate) fn collect_predicates(parsed: &p::Theory) -> Vec<p::Predicate> {
    parsed
        .items
        .iter()
        .filter_map(|i| {
            if let p::TheoryItem::Predicates(ps) = i {
                Some(ps.as_slice())
            } else {
                None
            }
        })
        .flatten()
        .cloned()
        .collect()
}

/// HS `prettyClosedProtoRule` over `theoryRules thy` (Web/Theory.hs:887-917, see line 894,898) —
/// one rendered rule string per user protocol rule, in source order.  Reuses
/// `render_rule` (the `--prove` theory-body rule printer) with the same
/// macro/arity1/manual-variant setup `pretty_closed_theory` uses.
pub fn web_proto_rules(parsed: &p::Theory, elaborated: &Theory) -> Vec<String> {
    let macros = collect_macros(parsed);
    let arity1 = arity1_noeq_names(elaborated);
    let manual_variants = contains_manual_rule_variants(parsed, elaborated, false);
    // Same positional `(name, occurrence)` pairing as `pretty_closed_theory`
    // — see `pair_elaborated_rules`.
    let elab_rules = pair_elaborated_rules(&parsed.items, elaborated);
    parsed
        .items
        .iter()
        .enumerate()
        .filter_map(|(idx, item)| match item {
            p::TheoryItem::Rule(r) => elab_rules[idx]
                .map(|er| render_rule(r, er, &macros, &arity1, manual_variants, false)),
            _ => None,
        })
        .collect()
}

/// HS `prettyRestriction` over `theoryRestrictions thy` (Web/Theory.hs:887-917, see line 895) —
/// one rendered restriction string per restriction, in source order.  Reuses
/// `render_parsed_restriction` (the `--prove` theory-body restriction printer).
pub fn web_restrictions(parsed: &p::Theory, elaborated: &Theory) -> Vec<String> {
    parsed
        .items
        .iter()
        .filter_map(|item| match item {
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                render_parsed_restriction(r, elaborated)
            }
            _ => None,
        })
        .collect()
}

/// Render HS `ppInjectiveFactInsts` (ClosedTheory.hs:413-418):
///
/// ```text
/// /*
/// looping facts with injective instances:
///   T1/n1, T2/n2, ...
/// */
/// ```
///
/// HS:
/// ```haskell
/// multiComment $ sep
///   [ text "looping facts with injective instances:"
///   , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]
/// ```
/// where `multiComment d = comment $ fsep [text "/*", d, text "*/"]`
/// (Theory/Text/Pretty.hs:102-103) and `fsepList pp = fsep . punctuate comma . map pp`
/// (Theory/Text/Pretty.hs:88-89).
///
/// Emits the empty string when no fact tags are injective.  Computes
/// the set on demand from the elaborated rules + reducible function
/// symbols — the same call `ProofContext::new` makes through `new_impl`
/// (`constraint/solver/context.rs`).
fn render_injective_fact_insts(elab: &Theory) -> String {
    use crate::fact::{FactTag, Multiplicity};
    use crate::pretty_hpj::{self as hpj, punctuate, Doc};
    let proto_rules: Vec<&crate::rule::ProtoRuleE> = elab.rules().map(|r| &r.rule).collect();
    let mut tags = crate::tools::injective_fact_instances::simple_injective_fact_instances(
        &proto_rules,
        &elab.signature.maude_sig.reducible_fun_syms_fast,
    );
    // HS `closeRuleCache` (CloseRule.hs:417-420): union the FORCED injective facts
    // (`setforcedInjectiveFacts {L_PureState, L_CellLocked}`,
    // lib/sapic/src/Sapic.hs:84) when
    // the state-channel optimisation is on.
    if elab.options.state_channel_opt {
        tags = crate::tools::injective_fact_instances::union_forced_injective_fact_instances(
            tags,
            &crate::tools::injective_fact_instances::pure_state_forced_fact_tags(),
        );
    }
    if tags.is_empty() {
        return String::new();
    }
    // HS `showFactTagArity` (Theory/Model/Fact.hs:556-557): persistent `!`-prefix + name
    // + `/` + arity.
    let label = |tag: &FactTag| -> String {
        let prefix = match tag {
            FactTag::Proto(Multiplicity::Persistent, _, _) => "!",
            _ => "",
        };
        format!(
            "{}{}/{}",
            prefix,
            crate::fact::fact_tag_name(tag),
            crate::fact::fact_tag_arity(tag)
        )
    };
    let tag_docs: Vec<Doc> = tags.iter().map(|(t, _)| Doc::text(label(t))).collect();
    // fsepList (text . showFactTagArity) (map fst tags)
    let list_doc = hpj::fsep(punctuate(Doc::text(","), tag_docs));
    // sep [text "looping facts...", nest 2 list_doc]
    let inner = hpj::sep(vec![
        Doc::text("looping facts with injective instances:"),
        list_doc.nest(2),
    ]);
    // multiComment inner = comment $ fsep [text "/*", inner, text "*/"]
    let doc = hpj::fsep(vec![Doc::text("/*"), inner, Doc::text("*/")]);
    doc.render()
}

// =============================================================================
// Signature
// =============================================================================

pub(crate) fn render_signature(sig: &tamarin_term::maude_sig::MaudeSig) -> String {
    let mut out = String::new();

    // builtins: ...  (only if any enabled)
    let mut builtins: Vec<&str> = Vec::new();
    if sig.enable_dh {
        builtins.push("diffie-hellman");
    }
    if sig.enable_bp {
        builtins.push("bilinear-pairing");
    }
    if sig.enable_mset {
        builtins.push("multiset");
    }
    if sig.enable_nat {
        builtins.push("natural-numbers");
    }
    if sig.enable_xor {
        builtins.push("xor");
    }
    if !builtins.is_empty() {
        // HS renders builtins via the same `ppNonEmptyList'` as functions:
        // `(keyword_ "builtins:" <->) . fsep . punctuate comma`
        // (Term/Maude/Signature.hs:252-263, see lines 261,263) — so the list wraps through
        // the HughesPJ engine, not a flat join.
        out.push_str(&wrap_with_lead("builtins:", &builtins));
        out.push('\n');
    }

    // functions: ...
    let funs = render_fun_syms(sig);
    if !funs.is_empty() {
        out.push_str(&wrap_with_lead("functions:", &funs));
        out.push('\n');
    }

    // equations: ...
    let eqs = render_equations(sig);
    if !eqs.is_empty() {
        let key = if sig.eq_convergent {
            "equations [convergent]:"
        } else {
            "equations:"
        };
        // HS uses `sep [hdr, nest 2 (punctuate comma ds)]` for the
        // equations list — yields `hdr\n    eq1,\n    eq2,...` when
        // multiple equations.
        out.push_str(&sep_block_with_lead(key, &eqs));
        out.push('\n');
    }

    out
}

/// Render the function symbol list: HS `prettyMaudeSigExcept` with an empty
/// exclusion set, i.e. the NoEq symbols in `S.toList` (BTreeSet) order
/// followed by the user-defined AC symbols, each with its space-prefixed
/// attribute list (`h/1 [destructor]`) and NDC attributes.
fn render_fun_syms(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<String> {
    sig.pretty_fun_syms_except(&std::collections::BTreeSet::new())
}

/// HS `prettyTranslationElement`, the two `FunctionTypingInfo` cases
/// (TheoryObject.hs:800-819 for a user-defined AC symbol, 820-838 for a free
/// one): the `function: f(t1, t2): t` typing line of a SAPIC theory, followed by
/// the symbol's attributes.
///
/// Intentionally retained: faithful mirror of those two cases, exercised only
/// by the unit tests below.  RS never produces
/// `TranslationElement::FunctionTypingInfo`.  In HS these items only reach a
/// printer through the OPEN theory (`typeTheoryEnv`
/// rebuilds them from the typing environment, Typing.hs:204-226, see line 210);
/// `removeTranslationItems` strips every translation item before a theory is
/// closed, so `--prove` output never carries them.  This is the faithful printer
/// for whenever open-theory rendering is ported.
///
/// SPACING.  HS glues the parts with `<->` = HughesPJ `<+>`, whose `text ""`
/// is a zero-width run rather than `empty`, so an ABSENT attribute still
/// contributes its separating space: a public constructor with no NDC state
/// renders `function: f (Any) : Any` plus three trailing spaces.  The
/// attribute strings themselves also carry a LEADING space in HS, which is why
/// a present `[private]` ends up two spaces from the out type.  `Doc::text_hs`
/// is the constructor that keeps an empty run present.
pub fn pretty_function_typing_info(fti: &crate::theory::SapicFunSym) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{fsep, parens, punctuate, Doc};
    use tamarin_term::function_symbols::{Constructability, NdcState, Privacy, UserDefinedSym};

    // HS `printType = maybe (text defaultSapicTypeS) text`.
    fn print_type(t: &crate::sapic::SapicType) -> Doc {
        match t {
            Some(ty) => Doc::text(ty),
            None => Doc::text(crate::sapic::default_sapic_type_string()),
        }
    }
    fn show_priv(p: Privacy) -> &'static str {
        match p {
            Privacy::Private => " [private]",
            Privacy::Public => "",
        }
    }
    fn show_const(c: Constructability) -> &'static str {
        match c {
            Constructability::Constructor => "",
            Constructability::Destructor => " [destructor]",
        }
    }
    fn show_ndc(n: NdcState) -> &'static str {
        match n {
            NdcState::NotNdc => "",
            NdcState::IsNdc => " [NDC]",
            NdcState::IsNdcDiff => " [NDC-Diff]",
            NdcState::IsNdcBoth => " [NDC,NDC-Diff]",
        }
    }

    let (privacy, constructability, ndc, is_ac) = match fti.sym {
        UserDefinedSym::NoEqUser(s) => (s.privacy, s.constructability, s.ndc, false),
        UserDefinedSym::AcFctUser(s) => (s.privacy, s.constructability, s.ndc, true),
    };
    let name = String::from_utf8_lossy(fti.sym.name());
    let args: Vec<Doc> = fti.arg_types.iter().map(print_type).collect();
    let mut d = Doc::text("function:")
        .beside_sp(Doc::text(name))
        .beside_sp(parens(fsep(punctuate(Doc::text(","), args))))
        .beside_sp(Doc::text(":"))
        .beside_sp(print_type(&fti.out_type));
    // The AC marker sits between the out type and the privacy attribute.
    if is_ac {
        d = d.beside_sp(Doc::text_hs(" [AC]"));
    }
    d = d.beside_sp(Doc::text_hs(show_priv(privacy)));
    d = d.beside_sp(Doc::text_hs(show_const(constructability)));
    d.beside_sp(Doc::text_hs(show_ndc(ndc)))
}

#[cfg(test)]
mod open_print_opts_tests {
    use super::*;
    use crate::sapic::{PlainProcess, Process, ProcessParsedAnnotation};

    fn no_conv(_: &p::Process) -> Result<PlainProcess, String> {
        Err("conv must not be called for overlaid/dropped items".to_string())
    }

    fn null_proc() -> PlainProcess {
        Process::Null(ProcessParsedAnnotation::empty())
    }

    fn render_item(item: &p::TheoryItem, st: &mut OpenPrintState<'_>) -> Vec<String> {
        // arity-1 set / predicates are irrelevant to the arms under test.
        #[allow(clippy::disallowed_types)]
        let arity1 = std::collections::HashSet::new();
        render_open_item(
            item,
            &[],
            "f.spthy",
            &arity1,
            &tamarin_term::maude_sig::pair_maude_sig(),
            &no_conv,
            st,
        )
        .unwrap()
    }

    fn fdecl(name: &str) -> p::FunctionDecl {
        p::FunctionDecl {
            name: name.to_string(),
            arg_types: vec![None],
            out_type: None,
            private: false,
            destructor: false,
            ac: false,
            ndc: false,
            ndc_diff: false,
        }
    }

    /// `msr`: every `TranslationElement` analogue renders empty
    /// (`removeTranslationItems` + `emptyString`, OpenTheory.hs:47-52,
    /// 891-898); non-translation items are untouched.
    #[test]
    fn drop_translation_items_zeroes_the_translation_element_set() {
        let opts = OpenPrintOpts {
            typed: None,
            extra_function_items: Vec::new(),
            drop_translation_items: true,
        };
        let mut st = OpenPrintState {
            opts: &opts,
            proc_idx: 0,
            def_idx: 0,
        };
        let dropped = [
            p::TheoryItem::Builtins(vec!["multiset".to_string()]),
            p::TheoryItem::Functions(vec![fdecl("h")]),
            p::TheoryItem::TopLevelProcess(p::Process::Null),
            p::TheoryItem::ProcessDef(p::ProcessDef {
                name: "P".to_string(),
                vars: None,
                body: p::Process::Null,
            }),
            p::TheoryItem::EquivLemma(p::Process::Null, p::Process::Null),
            p::TheoryItem::DiffEquivLemma(p::Process::Null),
            p::TheoryItem::Export {
                tag: "queries".to_string(),
                body: "q".to_string(),
            },
        ];
        for item in &dropped {
            assert!(
                render_item(item, &mut st).is_empty(),
                "expected empty render for {item:?}"
            );
        }
        // A non-translation item still renders.
        let keep = p::TheoryItem::FormalComment {
            header: String::new(),
            body: "keep".to_string(),
        };
        assert_eq!(
            render_item(&keep, &mut st),
            vec!["/*\nkeep\n*/".to_string()]
        );
    }

    /// `spthytyped`: process-bearing items render the OVERLAY processes (conv
    /// is never consulted), `ProcessDef` renders the overlay `(vars, body)` —
    /// `Some(vec![])` as the `let  P () =` empty parens — and
    /// source-positioned `Functions` items vanish
    /// (`clearFunctionTypingInfos`).
    #[test]
    fn typed_overlay_substitutes_processes_and_defs() {
        let opts = OpenPrintOpts {
            typed: Some(TypedOverlay {
                processes: vec![null_proc()],
                defs: vec![(Some(Vec::new()), null_proc())],
            }),
            extra_function_items: Vec::new(),
            drop_translation_items: false,
        };
        let mut st = OpenPrintState {
            opts: &opts,
            proc_idx: 0,
            def_idx: 0,
        };
        assert_eq!(
            render_item(&p::TheoryItem::TopLevelProcess(p::Process::Null), &mut st),
            vec!["process:\n  0".to_string()]
        );
        assert_eq!(
            render_item(
                &p::TheoryItem::ProcessDef(p::ProcessDef {
                    name: "P".to_string(),
                    vars: None,
                    body: p::Process::Null,
                }),
                &mut st
            ),
            vec!["let  P () = 0".to_string()]
        );
        assert!(render_item(&p::TheoryItem::Functions(vec![fdecl("h")]), &mut st).is_empty());
        assert_eq!(
            (st.proc_idx, st.def_idx),
            (1, 1),
            "one process and one def consumed"
        );
    }
}

#[cfg(test)]
mod function_typing_info_tests {
    use crate::theory::SapicFunSym;
    use tamarin_term::function_symbols::{
        AcFctSym, Constructability, NdcState, NoEqSym, Privacy, UserDefinedSym,
    };

    fn render(sym: UserDefinedSym, arg_types: Vec<Option<String>>) -> String {
        super::pretty_function_typing_info(&SapicFunSym {
            sym,
            arg_types,
            out_type: None,
        })
        .render()
    }

    /// A public constructor with no NDC state: the three absent attributes
    /// still contribute their `<+>` separator, so the line carries three
    /// trailing spaces.
    #[test]
    fn free_symbol_absent_attributes_keep_their_spaces() {
        let sym = NoEqSym::new(
            b"f".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        assert_eq!(
            render(UserDefinedSym::NoEqUser(sym), vec![None, None]),
            "function: f (Any, Any) : Any   "
        );
    }

    /// Declared argument types print verbatim, and each present attribute
    /// carries its own leading space on top of the separator.
    #[test]
    fn free_symbol_with_types_and_every_attribute() {
        let sym = NoEqSym::new(
            b"h".to_vec(),
            1,
            Privacy::Private,
            Constructability::Destructor,
        )
        .with_ndc(NdcState::IsNdcBoth);
        assert_eq!(
            render(UserDefinedSym::NoEqUser(sym), vec![Some("Key".to_string())]),
            "function: h (Key) : Any  [private]  [destructor]  [NDC,NDC-Diff]"
        );
    }

    /// The `[AC]` marker sits between the out type and the privacy attribute.
    #[test]
    fn user_ac_symbol_carries_the_ac_marker() {
        let sym = AcFctSym::new(
            b"g".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc,
        );
        assert_eq!(
            render(UserDefinedSym::AcFctUser(sym), vec![None, None]),
            "function: g (Any, Any) : Any  [AC]    [NDC]"
        );
    }
}

/// Render the equation list.  Each `CtxtStRule` has an LHS term and an
/// RHS term (after reading positions/term out of `StRhs`).  HS renders
/// `prettyCtxtStRule $ S.toList (stRules sig)` (Term/Maude/Signature.hs:252-259, see line 258),
/// i.e. equations in `S.toList` order.  `CtxtStRule` derives structural `Ord`,
/// so we emit them in the `st_rules` `BTreeSet` iteration order, which mirrors
/// HS's `S.toList` exactly.  We must NOT re-sort by the rendered pretty-string,
/// since that diverges from the structural (term-tree) order (e.g. AC products
/// pretty-print with a leading `(`, `exp` as infix `a^b`).
///
/// Each side is returned as a HughesPJ `Doc` (not a flat string) so that wide
/// function applications wrap at the ribbon width exactly as HS
/// `prettyCtxtStRule`/`prettyLNTerm` (SubtermRule.hs:123-126, Term/Term.hs:326-327)
/// — the `ppFun f ts = text (f++"(") <> fsep (punctuate comma …) <> ")"` `fsep`
/// breaks at argument boundaries when the term overruns.  We reach the Doc path
/// by converting the `LNTerm` to a parser-AST `p::Term` (`lnterm_to_parser`,
/// the same conversion already used elsewhere) and rendering it through
/// `pf::term_doc` (= HS `prettyTerm`).
fn render_equations(
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<(crate::pretty_hpj::Doc, crate::pretty_hpj::Doc)> {
    let mut items = Vec::new();
    for r in &sig.st_rules {
        let lhs = pf::term_doc(&lnterm_to_parser(&r.lhs));
        let rhs = pf::term_doc(&lnterm_to_parser(&r.rhs.term));
        items.push((lhs, rhs));
    }
    items
}

/// Port of HS `checkEquationsSubtermConvergence` (Wellformedness.hs:1222-1232).
///
/// HS works on `thyEquations thy = S.toList (stRules sig)` — the SIGNATURE's
/// subterm-rule Set, NOT the parser-AST `equations:` blocks.  The parser-level
/// `tamarin_parser::wf::subterm_convergence_report` approximates this on the
/// parser AST but (a) keeps the source order rather than the `Ord CtxtStRule`
/// Set order, and (b) renders each equation on a single flat line (no
/// width-wrapping), because the `tamarin-parser` crate has no access to the
/// HughesPJ engine.  This function — living in `tamarin-theory`, which has the
/// elaborated `MaudeSig` plus the ported HughesPJ printer — reproduces HS
/// byte-for-byte:
///
///   * order = `sig.st_rules` `BTreeSet` iteration = HS `S.toList` (derived
///     `Ord CtxtStRule`), so e.g. `f1, f2, f3, g` rather than source order
///     `f1, g, f2, f3`;
///   * each equation = `prettyCtxtStRule r = sep [nest 2 lhs, "=" <-> rhs]`
///     (SubtermRule.hs:122-123), rendered via `pf::term_doc` so a wide RHS
///     wraps (HS `prettyTerm`'s `fsep` ppFun, Term/Term.hs:326-327);
///   * suppressed entirely when `eqConvergent (sig thy)` is set
///     (`isUserMarkedConvergent`, Wellformedness.hs:1211-1214/1285).
///
/// `run.rs` calls this AFTER elaboration and REPLACES the parser-level entry
/// (same retain/re-add pattern used for "Message Derivation Checks").
pub fn subterm_convergence_report_wf(
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<tamarin_parser::wf::WfError> {
    use tamarin_parser::wf::{underline_topic, WfError};
    // HS: `if not (isUserMarkedConvergent thy) then checkEqs else []`
    // (Wellformedness.hs:1270-1286, see line 1285); `isUserMarkedConvergent thy = eqConvergent (sig thy)`.
    if sig.eq_convergent {
        return Vec::new();
    }
    // HS: `nonSubtermEquations = filterNonSubtermCtxtRule (thyEquations thy)`
    // = filter (not . isSubtermConvergentCtxtRule) (S.toList (stRules sig)).
    let non_conv: Vec<&tamarin_term::subterm_rule::CtxtStRule> = sig
        .st_rules
        .iter()
        .filter(|r| !tamarin_term::subterm_rule::is_subterm_convergent(r))
        .collect();
    if non_conv.is_empty() {
        return Vec::new();
    }

    // Equation list: `vcat (map prettyCtxtStRule nonSubtermEquations)`, each
    // `sep [nest 2 lhs, "=" <-> rhs]`, all rendered inside prettyWfErrorReport's
    // outer `nest 2`.  Build it as one HughesPJ Doc so the wrap decision +
    // indentation are HS-exact.
    //
    // WIDTH: the WF report Doc is rendered by HS `addComment c = ... TextItem
    // ("", render c)` (TheoryObject.hs:717-718, see line 718), where `render = P.render` uses the
    // HughesPJ DEFAULT style (`lineLength = 100`, `ribbonsPerLine = 1.5`,
    // `ribbon = round (100 / 1.5) = 67`) — NOT the theory body's
    // `renderDoc` width of 110/73 (Console.hs:242-243,398-399).  The pre-rendered
    // string is then emitted verbatim inside the `/* ... */` comment.  So the
    // equation list wraps at the 100/67 budget, e.g. `f3`/`f6` (inline width 73
    // from column 4) wrap while `f2` (66) stays inline.  This is a SEPARATE
    // width from the `equations:` block, which is part of the theory body and
    // renders at 110/73.
    const WF_LINE_LENGTH: usize = 100;
    const WF_RIBBON: usize = 67; // round(100 / 1.5)
    let eq_lines = {
        use crate::pretty_hpj::{self as hpj, Doc};
        let docs: Vec<Doc> = non_conv
            .iter()
            .map(|r| {
                let lhs = pf::term_doc(&lnterm_to_parser(&r.lhs)).nest(2);
                let rhs = pf::term_doc(&lnterm_to_parser(&r.rhs.term));
                let eq_doc = Doc::text("=").beside_sp(rhs);
                hpj::sep(vec![lhs, eq_doc])
            })
            .collect();
        // Outer `nest 2` from prettyWfErrorReport `(nest 2 . vcat ...)`.
        let mut s = hpj::vcat(docs)
            .nest(2)
            .render_with(WF_LINE_LENGTH, WF_RIBBON);
        s.push('\n');
        s
    };

    // Assemble the full message block (topic header + intro + equations +
    // footer) — byte-identical to the parser-level version, only `eq_lines`
    // differs (proper order + width-wrap).
    let mut msg = String::new();
    msg.push_str(&underline_topic("Subterm Convergence Warning"));
    msg.push('\n'); // blank line before intro (HS `$-$`)
    msg.push_str("  User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue \n");
    msg.push('\n'); // blank line after intro (HS `$-$` before vcat)
    msg.push_str(&eq_lines);
    // HS: `$-$ text " \n For more information..."` — note the leading space.
    msg.push_str("   \n For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html ");

    vec![WfError::new("Subterm Convergence Warning", msg)]
}

/// Format the `/* WARNING: ... */` or `/* All wellformedness checks
/// were successful. */` block that goes BETWEEN the source body and
/// the analysis summary.  Mirrors HS's `prettyWfErrorReport`
/// (Wellformedness.hs:118-125).
///
/// Each `WfError.message` is expected to carry the FULL HS-style block
/// for its topic: `Title\n=====\n\n<intro>\n<body>` — pre-formatted with
/// the exact bytes HS emits, including trailing spaces from HS's
/// `text ""` markers.  Consecutive `WfError`s with the same topic are
/// merged into one block (the per-clash bodies concatenated).  Topic
/// groups are separated by blank lines.
///
/// Shared by the `--prove` CLI (`run.rs`) and the interactive web server
/// (`source`/`message` routes) so both render the wellformedness comment
/// byte-identically.  The empty-report case returns exactly
/// `"/* All wellformedness checks were successful. */"`, so no-warning
/// theories stay byte-for-byte unchanged on both paths.
pub fn format_wf_block(report: &[tamarin_parser::wf::WfError]) -> String {
    if report.is_empty() {
        return "/* All wellformedness checks were successful. */".to_string();
    }
    let mut out = String::new();
    out.push_str("/*\nWARNING: the following wellformedness checks failed!\n\n");
    out.push_str(&render_wf_error_report(report));
    // Trim trailing blank lines but keep a single newline before `*/`.
    while out.ends_with("\n\n") {
        out.pop();
    }
    out.push_str("*/");
    out
}

/// Bare `prettyWfErrorReport` rendering (Wellformedness.hs:118-125) —
/// the grouped topic blocks WITHOUT the `/* WARNING ... */` comment
/// wrapper.  Shared by `format_wf_block` (batch theory output) and the
/// interactive server's `ppInteractive` console echo of the report at
/// theory-load time (Web/Dispatch.hs:149-209, see line 187,200-209).
pub fn render_wf_error_report(report: &[tamarin_parser::wf::WfError]) -> String {
    let mut out = String::new();
    // HS `groupOn fst = groupBy ((==) `on` fst)` (Extension/Prelude.hs:96-97)
    // splits the report into runs of CONSECUTIVE same-topic entries, so a topic
    // that reappears after an intervening one opens a SECOND group carrying its
    // own header.  Grouping every entry of a topic together instead would merge
    // those runs and drop the repeat.
    let mut groups: Vec<(&str, Vec<String>)> = Vec::new();
    for e in report {
        // A check whose body is HS's `fsep` paragraph fill hands over its cells
        // instead of a laid-out body, because the layout is HughesPJ's: see
        // `crate::wf_fill`.  Everything else pre-renders its own bytes.
        let body = match &e.fill {
            Some(fill) => crate::wf_fill::fill_body(fill),
            None => e.message.clone(),
        };
        match groups.last_mut() {
            Some((topic, msgs)) if *topic == e.topic => msgs.push(body),
            _ => groups.push((&e.topic, vec![body])),
        }
    }
    for (i, (topic, msgs)) in groups.iter().enumerate() {
        let topic = *topic;
        if i > 0 {
            out.push('\n');
        }
        // HS `prettyWfErrorReport` (Wellformedness.hs:118-125) groups by
        // topic and renders each group as
        //   `text topic $-$ (nest 2 . vcat . intersperse (text "") $ bodies)`
        // — the underlineTopic header ONCE per group, then the 2-space-nested
        // bodies separated by a 2-space blank line.  Most RS checks already
        // pre-render the FULL block (header + indent) into a per-topic
        // message, and the default path below concatenates those (dropping
        // the header copies past the first, which HS never repeats).
        //
        // Some checks emit one HEADER-LESS body per offending rule (so the
        // summary's `length rep` WARNING count stays HS-faithful,
        // Batch.hs:87-316, see line 245), all sharing one topic.  These are assembled HS-style
        // (`prettyWfErrorReport`, Wellformedness.hs:118-125): the topic header
        // (+ any "reasons" preamble that HS folds into the topic string) ONCE,
        // then the per-rule bodies joined by the `intersperse (text "")`
        // 2-space blank separator.  Other topics keep baking their full block
        // into each message (default path below).
        if let Some((preamble, nest_bodies)) = wf_headerless_preamble(topic) {
            out.push_str(&preamble);
            let bodies: Vec<String> = msgs
                .iter()
                .map(|m| {
                    if nest_bodies {
                        nest_wf_body(m)
                    } else {
                        m.clone()
                    }
                })
                .collect();
            out.push_str(&bodies.join("\n  \n"));
            out.push('\n');
        } else {
            // The bodies here bake the header in, one copy per entry, so a
            // multi-entry group sheds every copy but the first and falls back
            // on the group's own `intersperse (text "")` separator.
            let header = tamarin_parser::wf::underline_topic(topic);
            for (j, m) in msgs.iter().enumerate() {
                let mut body: &str = m;
                if j > 0 {
                    match body.strip_prefix(header.as_str()) {
                        // Shed the repeated header AND the blank line that
                        // `ppTopic`'s `$-$` puts between it and the body.
                        Some(rest) => {
                            out.push_str("  \n");
                            body = rest.strip_prefix('\n').unwrap_or(rest);
                        }
                        None => out.push('\n'),
                    }
                }
                out.push_str(body);
                if !body.ends_with('\n') {
                    out.push('\n');
                }
            }
        }
    }
    out
}

/// For the WF topics whose checks emit one header-less body per finding,
/// return the byte-exact preamble that `prettyWfErrorReport` prints ONCE
/// before the group's bodies: the `underlineTopic` header, plus the blank
/// line HS's `$-$`/topic-string folds in, plus (for the sort-clash topic)
/// the "Possible reasons" paragraph that HS appends to the topic string
/// (Wellformedness.hs:258-273).  Returns `None` for the topics that bake
/// their full block into each message (default path).
///
/// The `bool` says whether the bodies ALSO arrive without the `nest 2`
/// indent that `ppTopic` applies to every body of a group
/// (Wellformedness.hs:118-125, see line 125) — `true` means the renderer
/// supplies it.
fn wf_headerless_preamble(topic: &str) -> Option<(String, bool)> {
    use tamarin_parser::wf::underline_topic;
    match topic {
        // SAPIC-process wellformedness errors (HS `toWfErrorReport`,
        // Warnings.hs:23-26).  Unlike the other topics, HS does NOT underline
        // this one — `prettyWfErrorReport` renders it as a bare `text topic`
        // (Wellformedness.hs:118-125, see line 124).  So the per-error bodies (each
        // `"  Variable bound twice: x."`) sit directly under a plain header.
        "Wellformedness-error in Process" => Some((format!("{topic}\n"), false)),
        // These five bake the `nest 2` into their own bytes — the `Doc` fills
        // via `crate::wf_fill::fill_body`, `multRestrictedReport'`
        // (Wellformedness.hs:1047-1064) via `crate::mult_restricted`.  Their
        // bodies wrap at `sep`/`fsep` points that depend on the absolute
        // column, so the indent has to be inside the Doc the HughesPJ engine
        // lays out, not applied to the rendered lines afterwards.
        "Unbound variables"
        | "Reserved names"
        | "Special facts"
        | "Nat Sorts"
        | "Multiplication restriction of rules" => {
            Some((format!("{}\n", underline_topic(topic)), false))
        }
        // HS `freshFactArguments'` (Wellformedness.hs:569-576, see line 574)
        // pairs the underlined topic with a body that carries neither the
        // header nor the `nest 2` indent, so both come from here.
        "Fr facts must only use a fresh- or a msg-variable" => {
            Some((format!("{}\n", underline_topic(topic)), true))
        }
        "Variable with mismatching sorts or capitalization" => Some((
            format!(
                "{}\nPossible reasons:\n\
                 1. Identifiers are case sensitive, i.e.,\
                 'x' and 'X' are considered to be different.\n\
                 2. The same holds for sorts:, \
                 i.e., '$x', 'x', and '~x' are considered to be different.\n\n",
                underline_topic(topic)
            ),
            false,
        )),
        _ => None,
    }
}

/// Apply `prettyWfErrorReport`'s per-group `nest 2` to a body that arrives
/// without it: HS `nest` shifts EVERY line of the nested Doc, blank lines
/// included (Wellformedness.hs:118-125, see line 125).
fn nest_wf_body(body: &str) -> String {
    body.lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// HS `ppNonEmptyList' name pp xs = (keyword_ name <->) . fsep $
/// punctuate comma (map pp xs)` (Term/Maude/Signature.hs:261-263).
/// `<->` is HughesPJ `<+>` (beside-with-space), and `fsep` is the
/// fill-paragraph combinator, so the wrap decisions must come from the
/// ported HughesPJ Doc engine (LINE_LENGTH=110, RIBBON=73) — not a
/// hand-rolled greedy fill at a guessed width.  Route through `pretty_hpj`.
fn wrap_with_lead<S: AsRef<str>>(lead: &str, items: &[S]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() {
        return String::new();
    }
    let docs: Vec<Doc> = items.iter().map(Doc::text).collect();
    let body = hpj::fsep(hpj::punctuate(Doc::char(','), docs));
    // HS `ppNonEmptyList' name = (keyword_ name <->) . fsep`
    // (Term/Maude/Signature.hs:252-263, see line 261) — the `builtins:`/`functions:` lead is a
    // keyword.  `keyword_` is the identity in plain mode, so `--prove` is
    // unchanged.
    hpj::keyword_(lead).beside_sp(body).render()
}

/// HS `equations:` layout (Term/Maude/Signature.hs:256-258):
///   `P.sep ( keyword_ "equations:" : map (P.nest 2) ds )`
/// where `ds = P.punctuate P.comma (map prettyCtxtStRule rules)` — i.e. the
/// comma is appended to the END of each equation doc (all but the last), and
/// each resulting doc is `nest 2`'d, then `sep`-joined.
///
/// Each equation doc is itself (SubtermRule.hs:123-126):
///   `prettyCtxtStRule r = sep [ nest 2 (prettyLNTerm lhs)
///                             , operator_ "=" <-> prettyLNTerm rhs ]`
/// — so the LHS carries an *inner* `nest 2`.  When the outer `sep` breaks and
/// lays each equation on its own line at indent 2, the inner `nest 2` adds a
/// further 2, yielding the 4-space indent HS emits.  Reproducing that requires
/// the structured doc, not a pre-joined `lhs = rhs` string.  Route through the
/// ported HughesPJ engine so the break decision and indentation are HS-exact.
///
/// `items` carries the LHS/RHS as already-built term `Doc`s (HS `prettyLNTerm`)
/// so the inner function-application `fsep` wrapping survives — passing flat
/// strings would defeat the engine and emit over-long single lines for wide
/// equations (e.g. BP `idverify(idsign(…), m, IBPub(…))`).
fn sep_block_with_lead(
    lead: &str,
    items: &[(crate::pretty_hpj::Doc, crate::pretty_hpj::Doc)],
) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() {
        return String::new();
    }
    let n = items.len();
    let mut docs: Vec<Doc> = Vec::with_capacity(n + 1);
    // HS `keyword_ "equations:"` / `keyword_ "equations [convergent]:"`
    // (Term/Maude/Signature.hs:256-257).  Identity in plain mode.
    docs.push(hpj::keyword_(lead));
    for (i, (lhs, rhs)) in items.iter().enumerate() {
        // prettyCtxtStRule: sep [ nest 2 lhs, operator_ "=" <-> rhs ]
        let lhs_doc = lhs.clone().nest(2);
        let eq_doc = hpj::operator_("=").beside_sp(rhs.clone());
        let mut d = hpj::sep(vec![lhs_doc, eq_doc]);
        if i + 1 < n {
            d = d.beside(Doc::char(','));
        }
        docs.push(d.nest(2));
    }
    hpj::sep(docs).render()
}

// =============================================================================
// Item dispatch
// =============================================================================

/// Pair every parsed theory item with its elaborated rule, keyed by
/// `(name, occurrence-ordinal)` rather than by name alone — `None` for a
/// non-rule item and for a parsed rule with no elaborated counterpart.
///
/// One pass groups the elaborated rules by name (in theory order); the
/// occurrence ordinal of a parsed rule item among the earlier rule items of
/// the same name indexes straight into its group.
///
/// INVARIANT: for every rule name `N`, the k-th parsed rule item named `N`
/// corresponds to the k-th elaborated rule named `N`.
/// * Without partial evaluation rule names are unique (duplicates are a
///   parse error), so the ordinal is always 0 and this is exactly a
///   name-keyed lookup — including the no-variant drop (run.rs), which
///   removes a rule from the elaborated theory only: its parsed leftover
///   has zero elaborated occurrences and is not rendered.
/// * After `apply_partial_evaluation` names can repeat (one rule refining
///   into several); both item lists are then regenerated 1:1 from the same
///   refined-rule list in the same order, so same-name groups align
///   positionally.  A pass that drops refined rules from only ONE of the
///   two lists would break this alignment — drop from both, or not at all.
/// * After the auto-sources unfold (`auto_sources::unfold_rule_variants`) a
///   single-variant slot is regenerated 1:1 under its `___VARIANT_1` name
///   on both sides, while a MULTI-variant slot keeps the original parsed
///   rule (variant bodies parked in its `variants` field) against several
///   elaborated `___VARIANT_<i>` rules — that slot pairs with its first
///   variant via the fallback below.
fn pair_elaborated_rules<'a>(
    items: &[p::TheoryItem],
    elab: &'a Theory,
) -> Vec<Option<&'a crate::theory::OpenProtoRule>> {
    let mut by_name: tamarin_utils::FastMap<&str, Vec<&'a crate::theory::OpenProtoRule>> =
        Default::default();
    for er in elab.rules() {
        by_name.entry(er.name()).or_default().push(er);
    }
    let mut counts: tamarin_utils::FastMap<&str, usize> = Default::default();
    items
        .iter()
        .map(|item| match item {
            p::TheoryItem::Rule(r) => {
                let c = counts.entry(r.name.as_str()).or_default();
                let occ = *c;
                *c += 1;
                by_name
                    .get(r.name.as_str())
                    .and_then(|group| group.get(occ))
                    .copied()
                    .or_else(|| {
                        // Merged-display slot of a multi-variant auto-sources
                        // unfold (`unfold_rule_variants` parked the variant
                        // bodies in `r.variants` and no elaborated rule keeps
                        // the original name): anchor the slot to its k-th
                        // `___VARIANT_1` rule — every variant of one unfold
                        // carries the same loop breakers, so one anchor
                        // suffices for `render_unfolded_variants_block`.
                        if r.variants.is_empty() {
                            return None;
                        }
                        let vname = format!("{}___VARIANT_1", r.name);
                        by_name
                            .get(vname.as_str())
                            .and_then(|group| group.get(occ))
                            .copied()
                            .filter(|er| er.unfolded_variant)
                    })
            }
            _ => None,
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_parsed_item(
    item: &p::TheoryItem,
    elab_rule: Option<&crate::theory::OpenProtoRule>,
    macros: &[p::Macro],
    elab: &Theory,
    proved: &[ProvedLemma],
    in_file: &str,
    arity1: &std::collections::HashSet<String>,
    manual_variants: bool,
    auto_sources: bool,
) -> Option<String> {
    use p::TheoryItem::*;
    // `macros` is collected once by the caller (mirrors HS
    // `applyMacroInRestriction` + `parseLemmaWithMacros`, which store the
    // expanded formula separately from the original).
    match item {
        Builtins(_) | Functions(_) | Equations { .. } | Options(_) | Heuristic(_) | Tactic(_) => {
            // These are absorbed into the signature/configuration headers.
            None
        }
        Rule(r) => {
            // HS closeProtoRule (lib/theory/src/Rule.hs:82-86, see line 84): `ClosedProtoRule ruE <$>
            // maybeToList (variantsProtoRule hnd ruE)` — a rule with no
            // variants yields NO closed rule, so it is absent from the
            // closed theory and never rendered.  Such rules are removed
            // from the elaborated theory in run.rs; mirror the absence here.
            // The lookup is positional (`(name, occurrence)`) because
            // partial evaluation makes rule names non-unique.
            elab_rule.map(|er| {
                // Merged display of a multi-variant auto-sources unfold: the
                // paired rule is the slot's FIRST `___VARIANT_<i>` rule (see
                // `pair_elaborated_rules`), and the variant bodies live in
                // `r.variants` — HS's `prettyProtoRuleE ruE` + ` variants`
                // block (`prettyOpenProtoRuleAsClosedRule`'s merged branch,
                // OpenTheory.hs:845-851).
                if er.unfolded_variant && !r.variants.is_empty() {
                    render_unfolded_variants_block(r, er, arity1)
                } else {
                    render_rule(r, er, macros, arity1, manual_variants, auto_sources)
                }
            })
        }
        IntrRule(_) => None,
        Lemma(l) => render_parsed_lemma(l, proved, in_file, elab),
        // HS treats the deprecated `axiom` keyword as a synonym for
        // `restriction` (`liftedAddRestriction`; the legacy `axiom`/`Axiom` is
        // parsed and rendered as a `restriction`). RS already elaborates
        // `LegacyAxiom` as a restriction for solving; render it the same so the
        // deprecated-`axiom` blocks (e.g. the thesis-evoting auth models) emit
        // their `restriction <name>:` blocks instead of being dropped.
        Restriction(r) | LegacyAxiom(r) => render_parsed_restriction(r, elab),
        Predicates(preds) => {
            // HS `prettyTheory` folds each `PredicateItem` through
            // `prettyPredicate` (TheoryObject.hs:732-768, see line 764, 802-806):
            //   prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
            //     factstr    = render $ prettyFact prettyLVar (pFact p)
            //     formulastr = render $ prettyLNFormula      (pFormula p)
            // `kwPredicate = keyword_ "predicate"`, `<>` is no-space append and
            // `<->` is beside-with-space, so each predicate renders on its own
            // line as `predicate: <fact><=><formula>`.
            // Each `predicate` in a `predicates:` block is added as a SEPARATE
            // `PredicateItem` in HS (commaSep1 + foldM liftedAddPredicate,
            // Parser/Signature.hs:267-268), so the theory `vsep` separates them
            // with a blank line.  The Rust parser groups them into one
            // `Predicates` item, so we reproduce that blank-line separation by
            // joining the per-predicate lines with `\n\n`.
            if preds.is_empty() {
                return None;
            }
            let lines: Vec<String> = preds
                .iter()
                .map(|pr| render_predicate(pr, arity1))
                .collect();
            Some(lines.join("\n\n"))
        }
        Macros(macros) => {
            if macros.is_empty() {
                return None;
            }
            Some(render_parsed_macros(macros))
        }
        FormalComment { header, body } => {
            // HS `prettyFormalComment` (lib/theory/src/Pretty.hs:19-21):
            //   prettyFormalComment ""     body = multiComment_ [body]
            //   prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"
            // User `section{* .. *}` / `text{* .. *}` items always carry a
            // non-empty header, so they render verbatim as
            // `header{*body*}`.  (An empty header only arises from
            // machine-injected comments via `addComment`.)
            if header.is_empty() {
                Some(format!("/*\n{}\n*/", body))
            } else {
                Some(format!("{}{{*{}*}}", header, body))
            }
        }
        _ => None,
    }
}

// =============================================================================
// Rule
// =============================================================================

/// Names of arity-1 NoEq function symbols in the closed theory signature.
/// Mirrors HS `lookupArity` reading the parser-state signature for
/// `naryOpApp`'s `k == 1` tuple-folding (Theory/Text/Parser/Term.hs:88-96).
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn arity1_noeq_names(elab: &Theory) -> std::collections::HashSet<String> {
    crate::elaborate::arity1_noeq_names(elab.signature.maude_sig())
}

/// HS `openProtoRule` (lib/theory/src/Rule.hs:52-59) returns `OpenProtoRule ruE ruleAC`
/// where `ruleAC = []` iff `equalUpToTerms cprRuleAC cprRuleE` (i.e. the
/// closed rule's AC and E forms agree on fact TAGS + lengths,
/// Theory/Model/Rule.hs:887-895), else `ruleAC = [cprRuleAC]`.
///
/// `containsManualRuleVariants` (OpenTheory.hs:584-589) is True iff some
/// (merged) rule has a non-empty `ruleAC` — i.e. some rule's `openProtoRule`
/// yields the `[cprRuleAC]` branch.  `prettyClosedTheory`
/// (ClosedTheory.hs:382-418, see line 383) uses that to switch the WHOLE theory to the
/// "open-as-closed" renderer `prettyOpenProtoRuleAsClosedRule`
/// (OpenTheory.hs:827-851), which — for the `OpenProtoRule ruE []` (empty)
/// branch — emits NO `prettyLoopBreakers` line ("cannot show loop breakers
/// here, as we do not have the information"), whereas the
/// `OpenProtoRule _ [ruAC]` (non-empty) branch KEEPS the loop breakers.
///
/// This predicate is RS's per-rule mirror of "would `openProtoRule` yield a
/// non-empty `ruleAC`":
///   * Manual variants: a parsed `variants (modulo AC)` block on the input
///     rule produces `OpenProtoRule ruE (non-empty)` directly — always
///     counts, with or without `--auto-sources`.
///   * Unfolded VARIANT rules (`unfoldRuleVariants`, lib/theory/src/Rule.hs:63-79,
///     applied by the `--auto-sources` close): the AC name gains the
///     `___VARIANT_<i>` suffix while `cprRuleE` keeps the original, so
///     `equalUpToTerms` is False on the name alone → non-empty `ruleAC`.
///   * `--auto-sources`: `closeTheoryWithMaude` adds the synthetic
///     `AUTO_IN_*`/`AUTO_OUT_*` action facts to `cprRuleAC` ONLY (NOT
///     `cprRuleE` — `addActionClosedProtoRule`, lib/theory/src/Rule.hs:97-99), so an
///     AUTO-annotated rule has AC ≠ E up to fact tags → `equalUpToTerms`
///     False → non-empty `ruleAC`.  AC-variant substitution itself never
///     changes a fact's TAG, so the AUTO action is the only operation that
///     makes `equalUpToTerms` False here; "the elaborated rule carries an
///     `AUTO_*` action" is therefore exactly the auto-path discriminant.
///
/// Used both to compute the theory-level gate (OR over all rules) and, in
/// `render_rule`, to decide whether a trivial-AC-variant rule keeps or drops
/// its loop-breaker comment under the open renderer.
fn rule_open_ac_nonempty(
    parsed_rule: &p::Rule,
    elab_rule: Option<&crate::theory::OpenProtoRule>,
    auto_sources: bool,
) -> bool {
    // Manual `variants (modulo AC)` block on the input rule.
    if !parsed_rule.variants.is_empty() {
        return true;
    }
    // An unfolded VARIANT rule (auto-sources `unfoldRuleVariants`,
    // lib/theory/src/Rule.hs:63-79): its AC name (`<orig>___VARIANT_<i>`)
    // differs from its E name, so `equalUpToTerms`
    // (Theory/Model/Rule.hs:960-968) is False on the name alone and
    // `openProtoRule` yields the non-empty branch — with or without an
    // AUTO action.
    if elab_rule.is_some_and(|r| r.unfolded_variant) {
        return true;
    }
    if !auto_sources {
        // Non-auto path: HS does NOT unfold computed variants, and every
        // closed rule's AC form agrees with its E form up to terms, so
        // `openProtoRule` is always the empty branch.  Computed AC variants
        // do not count.
        return false;
    }
    // Auto path: the rule's AC form differs from its E form up to tags iff it
    // received an `AUTO_*` action.
    match elab_rule {
        None => false,
        Some(r) => r.rule.actions.iter().any(|f| {
            matches!(&f.tag, crate::fact::FactTag::Proto(_, name, _)
                if name.starts_with("AUTO_IN_") || name.starts_with("AUTO_OUT_"))
        }),
    }
}

/// HS `containsManualRuleVariants mergedRules` (OpenTheory.hs:584-589) as
/// computed by `prettyClosedTheory` (ClosedTheory.hs:382-418, see line 383, 402): True iff any
/// rule's `openProtoRule` yields a non-empty AC list.  See
/// [`rule_open_ac_nonempty`].  When True the theory renders via the
/// open-as-closed path, which suppresses loop-breaker comments on
/// trivial-AC-variant rules whose AC form equals their E form.
///
/// Each parsed rule item resolves to its elaborated counterpart by NAME
/// alone, not by the renderer's positional `(name, occurrence-ordinal)`
/// pairing ([`pair_elaborated_rules`]).  The two resolutions cannot disagree
/// here, because [`rule_open_ac_nonempty`] is constant across the elaborated
/// rules that share a name:
/// * Without `auto_sources` the elaborated rule is never read — the
///   predicate is the parsed item's own `variants` block, else False.
/// * With `auto_sources` it asks only whether the elaborated rule carries an
///   `AUTO_IN_*`/`AUTO_OUT_*` action, and those actions are attached BY
///   NAME: HS `addLabels` folds into a rule every act whose source rule has
///   the SAME NAME (`filter ((ruleName ru ==) . ruleName . fst3) acts`,
///   OpenTheory.hs:138-538, see line 359,364), and
///   [`crate::auto_sources::apply_auto_sources`] mirrors that, applying each
///   `(rule name, action)` pair to every elaborated rule of that name.  So
///   same-named rules always carry the same AUTO actions.
///
/// Same-named elaborated rules arise only two ways, and neither can break
/// that: [`crate::tools::apply_partial_evaluation`] refines ONE original
/// rule into several, and substitution leaves their action fact tags
/// identical; and a rule declaration repeated VERBATIM is admitted (HS
/// `addProtoRule`'s `maybe True (ruE ==)`, OpenTheory.hs:727-733), so its
/// copies are equal.  Any other duplicate name is the parser's
/// `duplicate rule: <name>` error.
fn contains_manual_rule_variants(
    parsed: &p::Theory,
    elaborated: &Theory,
    auto_sources: bool,
) -> bool {
    parsed.items.iter().any(|item| {
        if let p::TheoryItem::Rule(r) = item {
            let elab_rule = elaborated.rules().find(|er| er.name() == r.name);
            rule_open_ac_nonempty(r, elab_rule, auto_sources)
        } else {
            false
        }
    })
}

/// Apply the arity-1 surplus-arg pair-fold (HS `naryOpApp` `k == 1`,
/// Theory/Text/Parser/Term.hs:94-96) to every term in a parser-AST fact.  Thin alias over the
/// shared [`crate::elaborate::rewrite_arity1_fact`] so the rule
/// pretty-printer and the lemma/formula paths share one implementation.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn rewrite_arity1_fact(fa: &p::Fact, arity1: &std::collections::HashSet<String>) -> p::Fact {
    crate::elaborate::rewrite_arity1_fact(fa, arity1)
}

/// HS `prettyMacros` / `prettyMacro` (TheoryObject.hs:862-884).
///
/// HS: `prettyMacros m = keyword_ "macros:" $$ nest 4 (vcat [macros...])`
/// HS: `prettyMacro (op, args, out) =
///       vcat [ppNonEmptyList (\ds -> sep (map (nest 4) ds)) text [op++"("]
///             <-> prettyVarList args <-> text ") = " <-> prettyTerm show out]`
///
/// `ppNonEmptyList hdr pp [x] = hdr [pp x] = sep [nest 4 (text x)]`
/// = `nest 4 (text (name++"("))`.
///
/// With `keyword_ "macros:" $$ nest 4 (nest 4 "name(" <+> args <+> ") = " <+> body)`:
/// the double-nest (8 total) combined with `keyword_`'s 7-char width makes
/// `nil_above_nest` inline the content (k = -7+8 = 1 > 0), putting everything
/// on ONE line: `macros: name( args ) =  body`.
///
/// For multiple macros, each is nested 4 levels inside the outer `nest 4`,
/// giving 8-space indent on subsequent lines.
fn render_parsed_macros(macros: &[p::Macro]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};

    let last_idx = macros.len() - 1;
    let macro_docs: Vec<Doc> = macros
        .iter()
        .enumerate()
        .map(|(i, m)| {
            // HS: `ppNonEmptyList (\ds -> sep (map (nest 4) ds)) text [op++"("]`
            // = `sep [nest 4 (text (op ++ "("))]` = `nest 4 (text (op ++ "("))`.
            let name_open = Doc::text(format!("{}(", m.name)).nest(4);
            // HS: `prettyVarList args = fsep . punctuate comma . map prettyLVar`
            // For macro args (bare LVar names, sort-prefix from hint):
            let args_parts: Vec<String> = m
                .args
                .iter()
                .map(|v| {
                    let mut s = tamarin_term::lterm::sort_prefix(v.sort).to_string();
                    s.push_str(&v.name);
                    if v.idx > 0 {
                        s.push('.');
                        s.push_str(&v.idx.to_string());
                    }
                    s
                })
                .collect();
            let args_str = args_parts.join(", ");
            // HS: `prettyTerm (text . show) body`
            let body_str = pf::pretty_term(&m.body);
            // Build: `nest 4 "name(" <+> args <+> ") = " <+> body`
            // HS <-> = HughesPJ <+> (beside with space = beside_sp).
            let mut doc = name_open;
            if !m.args.is_empty() {
                doc = doc.beside_sp(Doc::text(args_str));
            }
            doc = doc.beside_sp(Doc::text(") = "));
            doc = doc.beside_sp(Doc::text(body_str));
            // HS: last macro has no trailing comma
            if i < last_idx {
                doc.beside(Doc::text(","))
            } else {
                doc
            }
        })
        .collect();

    // HS: `keyword_ "macros:" $$ nest 4 (vcat macro_docs)`
    let body = hpj::vcat(macro_docs).nest(4);
    let header = Doc::text("macros:");
    header.above(body).render()
}

/// Render the `macros:` block for HS `rulesSnippet`'s first `ppWithHeader
/// "Macros"` (Web/Theory.hs) — the interactive `main/rules` page.  Returns
/// `None` when the theory declares no macros (HS omits the whole section),
/// else the same `prettyMacros` string the `--prove` theory body uses
/// ([`render_parsed_macros`]); rendered at the caller's active display width.
pub fn web_macros(parsed: &p::Theory) -> Option<String> {
    let macros: Vec<p::Macro> = collect_macros(parsed);
    if macros.is_empty() {
        None
    } else {
        Some(render_parsed_macros(&macros))
    }
}

/// Render a rule's attribute block `[...]`, mirroring HS `prettyRuleAttributes`
/// / `prettyRuleAttribute` (Model/Rule.hs:1314-1334).  HS emits a FIXED-order
/// `catMaybes [color, process, no_derivcheck, issapicrule, role]` joined by
/// `fsep . punctuate comma` (", "), wrapped in `[`..`]`; empty → nothing.
/// External (`x-…`) attributes are NOT in HS's list, so they are dropped.
/// Build HS `prettyRuleAttribute`'s ordered part list (Model/Rule.hs:1314-1321).
///
/// HS stores the parsed attribute LIST folded into a `RuleAttributes` STRUCT via
/// its `Semigroup` (Model/Rule.hs:382-396): for the `Maybe`-typed fields
/// (`ruleColor`, `role`) `preferRight a b = if isJust b then b else a` ⇒ the
/// LAST occurrence wins.  RS therefore takes the LAST match, not the first
/// (`rev().find_map(..)`).  `no_derivcheck`/`issapicrule` are booleans combined
/// with `||`, so order-independent (`.any(..)`).
///
/// Render order is the `catMaybes [color, process, no_derivcheck, issapicrule,
/// role]` of `prettyRuleAttribute`.  HS's attribute parser `parseAndIgnore`s
/// `process=` (Parser/Rule.hs:68-93, see line 72), so a user-written `process=` never sets
/// `ruleProcess` and is never rendered; RS mirrors this by discarding `process=`
/// at parse time.  [`p::RuleAttr::Process`] is synthesised only by the SAPIC
/// translation on the rules it generates (`tamarin_sapic::apply`), matching
/// HS's `ruleProcess`.
fn rule_attribute_parts(attrs: &[p::RuleAttr]) -> Vec<String> {
    let mut parts: Vec<String> = Vec::new();
    // color= : HS `text "color=" <> text (rgbToHex c)`; `rgbToHex` is
    // `'#':` + lowercase 2-digit-per-channel hex (Data/Color.hs:140-147, see line 141).
    if let Some(hex) = attrs.iter().rev().find_map(|a| match a {
        p::RuleAttr::Color(c) => Some(c),
        _ => None,
    }) {
        parts.push(format!(
            "color=#{}",
            hex.trim_start_matches('#').to_lowercase()
        ));
    }
    // process= : HS `ppProcess p = text "process=" <> "\"" ++ topLevel ++ "\""`
    // (Model/Rule.hs:1324-1327, see line 1324).  Rendered between color= and no_derivcheck.  Only
    // SAPIC-translation-generated rules carry it (the parser ignores a
    // user-written `process=`); the LAST occurrence wins (Maybe field).
    if let Some(s) = attrs.iter().rev().find_map(|a| match a {
        p::RuleAttr::Process(s) => Some(s),
        _ => None,
    }) {
        parts.push(format!("process=\"{}\"", s));
    }
    if attrs.iter().any(|a| matches!(a, p::RuleAttr::NoDerivCheck)) {
        parts.push("no_derivcheck".to_string());
    }
    if attrs.iter().any(|a| matches!(a, p::RuleAttr::IsSapicRule)) {
        parts.push("issapicrule".to_string());
    }
    if let Some(r) = attrs.iter().rev().find_map(|a| match a {
        p::RuleAttr::Role(r) => Some(r),
        _ => None,
    }) {
        parts.push(format!("role='{}'", r));
    }
    parts
}

/// Build the `prettyRuleAttributes` Doc (Model/Rule.hs:1330-1334):
///   `mempty == ruleAttributes ⇒ emptyDoc`,
///   else `hcat [text "[", prettyRuleAttribute ru, text "]"]`,
/// where `prettyRuleAttribute = fsep $ punctuate comma [..]`.  Returning a Doc
/// (not a flat string) lets the enclosing rule-header line wrap the attribute
/// list via `fsep` at the ribbon width, exactly as HughesPJ does for HS.
pub(crate) fn rule_attributes_doc(attrs: &[p::RuleAttr]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let parts = rule_attribute_parts(attrs);
    if parts.is_empty() {
        return Doc::empty();
    }
    let part_docs: Vec<Doc> = parts.into_iter().map(Doc::text).collect();
    // `fsep $ punctuate comma [..]` — comma is `text ","`, and the `fsep`
    // continuation hangs at the column right after `[` (beside, no space).
    let inner = hpj::fsep(hpj::punctuate(Doc::text(","), part_docs));
    Doc::text("[").beside(inner).beside(Doc::text("]"))
}

/// The `rule (modulo E) NAME[attrs]:` header line plus the 3-space-indented
/// `[ prems ] --[ acts ]-> [ concs ]` body, i.e. HS `prettyProtoRuleE`
/// (Model/Rule.hs:1280-1292 `prettyNamedRule` with the `(modulo E)` prefix).
/// Also returns the arity-1-folded fact rows so `render_rule`'s
/// trivial-AC-variant comparison can reuse them.
///
/// Shared by the closed renderer (`render_rule`, which appends the
/// AC-variant/loop-breaker annotations) and the open `--parse-only` renderer
/// (`render_open_rule`, which appends nothing — `prettyOpenProtoRule`'s
/// `OpenProtoRule ruE []` branch, OpenTheory.hs:815-816).
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_rule_e_block(
    parsed_rule: &p::Rule,
    arity1: &std::collections::HashSet<String>,
) -> (String, Vec<p::Fact>, Vec<p::Fact>, Vec<p::Fact>) {
    let name = &parsed_rule.name;
    let mut out = String::new();
    // HS rule-header line (`prettyNamedRule`, Model/Rule.hs:1280-1292, see line 1285):
    //   `prefix <-> prettyRuleName ru <> prettyRuleAttributes ru <> colon`
    // i.e. `"rule (modulo E)" <+> name <> [attrs] <> ":"`.  Routed through the
    // HughesPJ-faithful Doc engine so the attribute list's `fsep` wraps at the
    // ribbon width (the continuation hangs right after the `[`), byte-identical
    // to HS.  `<->`/`<+>` = space, `<>` = no space.
    {
        use crate::pretty_hpj::Doc;
        let header = crate::pretty_hpj::kw_rule_modulo("E")
            .beside_sp(Doc::text(name.clone()))
            .beside(rule_attributes_doc(&parsed_rule.attributes))
            .beside(Doc::text(":"));
        out.push_str(&header.render());
        out.push('\n');
    }
    let (premises, actions, conclusions) = display_fact_rows(parsed_rule, arity1);
    out.push_str(&render_rule_body(&premises, &actions, &conclusions));
    (out, premises, actions, conclusions)
}

/// A parsed rule's display fact rows `(premises, actions, conclusions)` —
/// the form every closed-rule comparison and render works on.  Shared by
/// `render_rule_e_block` and the `--auto-sources` variant unfold's
/// triviality test (`auto_sources::unfold_rule_variants`), so the two agree
/// byte-for-byte on what the rule displays as.
///
/// Desugars `let x = t in ...` bindings first — HS does this via
/// `applyMacroInProtoRule`/`expandRuleLetBlock` so the emitted rule contains
/// no bound names from the `let` block.  Mirrors `apply_let_block`
/// (`elaborate.rs`).  HS site: `lib/theory/src/TheoryObject.hs::prettyTheory`
/// → `prettyRule` chain which operates on the post-`applyMacroInProtoRule`
/// rule.
///
/// Then re-folds arity-1 comma lists: an arity-1 function applied as
/// `f(a,b,c)` is folded by `naryOpApp`'s `k == 1` branch into `f(<a,b,c>)`
/// (Theory/Text/Parser/Term.hs:94-96).  RS's term parser keeps the surplus
/// args, so re-fold here before rendering.  See `rewrite_arity1_term`.
/// `arity1` is computed once by the caller and threaded in.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub(crate) fn display_fact_rows(
    parsed_rule: &p::Rule,
    arity1: &std::collections::HashSet<String>,
) -> (Vec<p::Fact>, Vec<p::Fact>, Vec<p::Fact>) {
    let desugared = crate::elaborate::apply_let_block(parsed_rule);
    let premises: Vec<p::Fact> = desugared
        .premises
        .iter()
        .map(|f| rewrite_arity1_fact(f, arity1))
        .collect();
    let actions: Vec<p::Fact> = desugared
        .actions
        .iter()
        .map(|f| rewrite_arity1_fact(f, arity1))
        .collect();
    let conclusions: Vec<p::Fact> = desugared
        .conclusions
        .iter()
        .map(|f| rewrite_arity1_fact(f, arity1))
        .collect();
    (premises, actions, conclusions)
}

// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_rule(
    parsed_rule: &p::Rule,
    elab_rule: &crate::theory::OpenProtoRule,
    macros: &[p::Macro],
    arity1: &std::collections::HashSet<String>,
    manual_variants: bool,
    auto_sources: bool,
) -> String {
    let name = &parsed_rule.name;
    let (mut out, premises, actions, conclusions) = render_rule_e_block(parsed_rule, arity1);

    // `elab_rule` is the elaborated counterpart of `parsed_rule`, resolved
    // by the caller's positional pairing (`pair_elaborated_rules`) — it decides
    // between "trivial AC variant" and the full `/* rule (modulo AC) ... */`
    // block.  HS-faithful: matches `prettyClosedProtoRule`
    // (ClosedTheory.hs:332-363); the test itself is the shared
    // `is_trivial_proto_variant_ac` (also the auto-sources unfold's gate).
    let trivial = is_trivial_proto_variant_ac(&premises, &actions, &conclusions, elab_rule, macros);

    // HS `prettyClosedProtoRule` (ClosedTheory.hs:337-339, 352-354) emits
    // `prettyLoopBreakers` at `nest 2` BEFORE the trailing
    // `multiComment_` (trivial) or `multiComment (prettyProtoRuleAC ...)`
    // (non-trivial) block.  We emit the same `  // loop breaker: [<n>]`
    // / `  // loop breakers: [<n>,<m>]` line here when non-empty.
    //
    // HS gate (ClosedTheory.hs:382-418, see line 383): when `containsManualRuleVariants` holds
    // the whole theory renders via `prettyOpenProtoRuleAsClosedRule`
    // (OpenTheory.hs:827-851).  Its trivial-AC-variant branch
    // `(OpenProtoRule ruE [])` (OpenTheory.hs:828-835) shows NO loop-breaker
    // line ("cannot show loop breakers here, as we do not have the
    // information"), while the `(OpenProtoRule _ [ruAC])` branch
    // (OpenTheory.hs:836-843) KEEPS them.  A rule lands in the empty branch
    // iff its `openProtoRule` AC list is empty — see `rule_open_ac_nonempty`.
    // So under the gate, suppress the loop-breaker comment on a
    // trivial-AC-variant rule whose AC form equals its E form (no manual
    // variants, no AUTO action).  Without the gate the closed renderer
    // (`prettyClosedProtoRule`) always shows them — unchanged.
    let open_ac_nonempty = rule_open_ac_nonempty(parsed_rule, Some(elab_rule), auto_sources);
    let show_loop_breakers = !manual_variants || open_ac_nonempty;
    let outer_loop_breaker = if show_loop_breakers {
        render_loop_breakers_line(&elab_rule.loop_breakers, 2)
    } else {
        String::new()
    };
    if trivial {
        out.push_str("\n\n");
        out.push_str(&outer_loop_breaker);
        // HS trivial branch: `nest 2 (multiComment_ ["has exactly the trivial
        // AC variant"])` (ClosedTheory.hs:337-339).  In HtmlDoc mode this yields
        // an `hl_comment` span; in plain mode `multi_comment_` renders exactly
        // `/* has exactly the trivial AC variant */` (single line at this width).
        out.push_str("  ");
        out.push_str(
            &crate::pretty_hpj::multi_comment_(&["has exactly the trivial AC variant"]).render(),
        );
    } else {
        out.push_str("\n\n");
        out.push_str(&outer_loop_breaker);
        out.push_str(&render_ac_variants_block(
            name,
            elab_rule,
            &parsed_rule.attributes,
        ));
    }
    out
}

/// The merged display of a multi-variant auto-sources unfold — HS
/// `prettyOpenProtoRuleAsClosedRule (OpenProtoRule ruE variants)`
/// (OpenTheory.hs:845-851):
///   `prettyProtoRuleE ruE $-$ nest 1 (kwVariants $-$ nest 1 (ppList
///   prettyProtoRuleAC variants))`
/// — the E rule at its usual columns, a ` variants` keyword line (nest 1),
/// then each variant as `prettyProtoRuleAC` at nest 2 (header at col 2,
/// body bracket at col 5, its `ProtoRuleACInfo` at col 4), separated by a
/// `,` line at col 2.  For an unfolded variant the info prints only the
/// carried loop breakers — the disjunction is `[emptySubstVFresh]`, which
/// `ppVariants` elides (Theory/Model/Rule.hs:1407-1413, see line 1412) —
/// and every variant of one unfold carries the SAME breakers, so the
/// slot's single elaborated anchor (`er`, its first variant — see
/// `pair_elaborated_rules`) supplies them for all.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_unfolded_variants_block(
    parsed_rule: &p::Rule,
    er: &crate::theory::OpenProtoRule,
    arity1: &std::collections::HashSet<String>,
) -> String {
    use crate::elaborate::canonicalize_ac_in_pfact;
    use crate::pretty_hpj::Doc;
    let (mut out, _, _, _) = render_rule_e_block(parsed_rule, arity1);
    out.push('\n');
    out.push(' ');
    out.push_str(&crate::pretty_hpj::keyword_("variants").render());
    for (i, v) in parsed_rule.variants.iter().enumerate() {
        out.push('\n');
        if i > 0 {
            out.push_str("  ,\n");
        }
        let header = crate::pretty_hpj::kw_rule_modulo("AC")
            .beside_sp(Doc::text(v.name.clone()))
            .beside(rule_attributes_doc(&v.attributes))
            .beside(Doc::text(":"))
            .nest(2);
        out.push_str(&header.render());
        out.push('\n');
        // The variant bodies were regenerated from LN facts
        // (`proto_rule_to_parsed`), so canonicalise AC argument order at
        // render time exactly as the modulo-AC comment block does.
        let prems: Vec<p::Fact> = v.premises.iter().map(canonicalize_ac_in_pfact).collect();
        let acts: Vec<p::Fact> = v.actions.iter().map(canonicalize_ac_in_pfact).collect();
        let concs: Vec<p::Fact> = v.conclusions.iter().map(canonicalize_ac_in_pfact).collect();
        let body = render_rule_body_at(&prems, &acts, &concs, 5);
        out.push_str(body.trim_end_matches('\n'));
        let breakers = render_loop_breakers_line(&er.loop_breakers, 4);
        if !breakers.is_empty() {
            out.push('\n');
            out.push_str(breakers.trim_end_matches('\n'));
        }
    }
    out
}

/// Render HS's `prettyLoopBreakers` (Theory/Model/Rule.hs:1418-1424):
///
/// ```haskell
/// prettyLoopBreakers i = case breakers of
///     []  -> emptyDoc
///     [_] -> lineComment_ $ "loop breaker: "  ++ show breakers
///     _   -> lineComment_ $ "loop breakers: " ++ show breakers
///   where breakers = getPremIdx <$> L.get pracLoopBreakers i
/// ```
///
/// `lineComment_ s = comment $ text "//" <-> text s` → `// <s>`.  Haskell
/// `show` on `[Int]` produces `[i,j,k]` with NO spaces after commas.
/// The trailing `\n` lets the next line attach.
fn render_loop_breakers_line(breakers: &[crate::rule::PremIdx], indent: usize) -> String {
    if breakers.is_empty() {
        return String::new();
    }
    let plural = if breakers.len() == 1 { "" } else { "s" };
    let idxs: Vec<String> = breakers.iter().map(|b| b.0.to_string()).collect();
    let body = format!("loop breaker{}: [{}]", plural, idxs.join(","));
    // HS `prettyLoopBreakers` emits this via `lineComment_`
    // (Theory/Model/Rule.hs:1419-1429, see line 1421,1429), so the HtmlDoc pane render wraps it in an
    // `hl_comment` span; the plain render is the bare `// …` text.
    format!(
        "{}{}\n",
        " ".repeat(indent),
        crate::pretty_hpj::line_comment_(&body).render()
    )
}

/// HS `isTrivialProtoVariantAC ruAC ruE` (Model/Rule.hs:790-793):
///   variants == [emptySubstVFresh] && ps == ps' && cs == cs' && as == as' && nvs == nvs'
///
/// i.e. trivial iff (a) the variant disjunction is just the identity
/// AND (b) the AC-normalised rule body equals the E-rule body
/// structurally.  Even when there are NO non-trivial substitutions
/// to enumerate, the AC normalisation may have rewritten terms
/// (e.g. `'g'^~ltkB^~ltkA` → `'g'^(~ltkA*~ltkB)` under DH), in which
/// case HS prints the AC body as a comment block rather than the
/// trivial-variant annotation.
///
/// Evaluated here on RS's split representation: `elab_rule` carries the
/// variant machinery, and `display_*` are the parsed rule's display fact
/// rows ([`display_fact_rows`]) standing in for HS's `cprRuleE` half.
/// Shared by `render_rule` (trivial comment vs `rule (modulo AC)` block,
/// `prettyClosedProtoRule`, ClosedTheory.hs:332-363) and the
/// `--auto-sources` variant unfold's gate
/// (`auto_sources::unfold_rule_variants`, HS lib/theory/src/Rule.hs:63-79)
/// so the two can never disagree on triviality.
///
/// MACRO CASE (ClosedTheory.hs:332-366, see line 334 + Model/Rule.hs:790-793): When the theory
/// uses macros, HS's `cprRuleE` keeps the MACRO form of the rule while
/// `cprRuleAC` has the EXPANDED form (closeProtoRule runs
/// `applyMacroInRule` before `variantsProtoRule` but stores the original
/// `ruE` untouched — lib/theory/src/Rule.hs:82-86, see line 85).
/// `isTrivialProtoVariantAC` then
/// returns `False` because `ps != ps'` (macro term ≠ expanded term).
/// RS's `opr.rule` stores the EXPANDED form (post-`expand_theory_macros`)
/// so we must additionally check whether the DISPLAY form (parsed_rule,
/// which still has macro calls) matches the elaborated body.  If they
/// differ, even a rule with no AC variants must show the AC comment block
/// containing the expanded form.
pub(crate) fn is_trivial_proto_variant_ac(
    display_premises: &[p::Fact],
    display_actions: &[p::Fact],
    display_conclusions: &[p::Fact],
    elab_rule: &crate::theory::OpenProtoRule,
    macros: &[p::Macro],
) -> bool {
    let no_residual_substs = elab_rule.variant_substs.iter().all(|s| s.is_empty());
    // In HS, `cprRuleE` (E-rule) and `cprRuleAC` (AC-rule) live in
    // the SAME term universe — AC smart-constructors normalise at
    // construction time everywhere, so the only difference between
    // them arises from (a) genuine non-trivial AC variants or (b)
    // macro expansion changing terms.
    //
    // In RS: `abstracted_rule = Some(ac)` iff Maude found a
    // non-trivial abstraction (reducible sub-terms, yielding a
    // different AC form) — compare the E-rule against the abstracted
    // AC form via `same_rule_body`.
    // `abstracted_rule = None` means `abstract_rule_and_variants`
    // returned `Ok(None)` (common_subst empty AND no residual
    // substs) — i.e., the AC form IS the E form.  The only remaining
    // source of divergence is macro expansion: if the display body
    // contains macro calls, it differs from the
    // elaborated form and HS's `ps != ps'` would fire.  Detect this
    // by applying macros to the display facts and checking whether
    // any term changed (HS `applyMacroInRule`, lib/theory/src/Rule.hs:85).
    //
    // Crucially: do NOT compare rendered text across AST↔LN spaces —
    // AC ordering and nat-constant representation differ between the
    // parsed form and `lnfacts_to_parser(elab_rule.rule.*)`, producing
    // false negatives for plain rules like those in ParserTests.spthy.
    //
    // The macro check holds REGARDLESS of whether
    // Maude abstracted the rule, so it MUST gate BOTH branches below:
    // a rule that is both macro-using AND abstracted (e.g. a `^`/DH
    // rule whose body is a macro call) is NOT trivial
    // (regression/trace/issue777: `pk(x)='g'^x`, `Out(pk(~x))`).
    // Fast path: with no macro definitions, `apply_macros_fact` is an
    // identity rebuild (no macro can match), so the comparison below is
    // always `true`.  Skip the three deep-clone passes entirely.
    let no_macro_in_display = macros.is_empty() || {
        let mp: Vec<p::Fact> = display_premises
            .iter()
            .map(|f| crate::macro_expand::apply_macros_fact(macros, f))
            .collect();
        let ma: Vec<p::Fact> = display_actions
            .iter()
            .map(|f| crate::macro_expand::apply_macros_fact(macros, f))
            .collect();
        let mc: Vec<p::Fact> = display_conclusions
            .iter()
            .map(|f| crate::macro_expand::apply_macros_fact(macros, f))
            .collect();
        mp == display_premises && ma == display_actions && mc == display_conclusions
    };
    let ac_body_matches = match &elab_rule.abstracted_rule {
        // No Maude abstraction: AC form == E form structurally, so
        // trivial iff no macro changes the display body.
        None => no_macro_in_display,
        // Maude abstracted the rule: the AC (abstracted) body must
        // match the elaborated body AND no macro may differ between
        // the display (E) and expanded (AC) forms.
        Some(ac) => same_rule_body(&elab_rule.rule, ac) && no_macro_in_display,
    };
    no_residual_substs && ac_body_matches
}

/// Compare the `(premises, conclusions, actions, new_vars)` of two
/// `ProtoRuleE` rules structurally.  Mirrors HS's
/// `isTrivialProtoVariantAC` body equality check (Model/Rule.hs:790-793, see line 793):
/// `ps == ps' && cs == cs' && as == as' && nvs == nvs'`.
///
/// Used by `render_rule` to decide whether the AC-normalised rule body
/// differs from the E-rule body — when it does, even an empty variant
/// disjunction must be rendered as a `/* rule (modulo AC) ... */`
/// comment block (since the AC form is observably different).
fn same_rule_body(a: &crate::rule::ProtoRuleE, b: &crate::rule::ProtoRuleE) -> bool {
    use crate::fact::LNFact;
    let same_facts = |xs: &[LNFact], ys: &[LNFact]| {
        xs.len() == ys.len()
            && xs
                .iter()
                .zip(ys.iter())
                .all(|(f1, f2)| f1.tag == f2.tag && f1.terms == f2.terms)
    };
    same_facts(&a.premises, &b.premises)
        && same_facts(&a.conclusions, &b.conclusions)
        && same_facts(&a.actions, &b.actions)
        && a.new_vars == b.new_vars
}

/// Render `[ prems ] --[ acts ]-> [ concs ]` body shared between the
/// modulo-E and modulo-AC renderers.  Tries single-line layout first;
/// when it overflows the 76-col threshold, wraps each clause to its own
/// line as HS's `prettyRuleRestrGen` does via `sep`.
fn render_rule_body(prems: &[p::Fact], acts: &[p::Fact], concs: &[p::Fact]) -> String {
    // AC-canonicalise the rule body BEFORE rendering — the parser produces
    // left-associative nested `BinOp(Xor, BinOp(Xor, na, k), nb)` for
    // `na ⊕ k ⊕ nb`, but HS's `fAppAC` at parse time flattens and sorts
    // the multiset, producing a different visual order (`k ⊕ nb ⊕ na`).
    // We apply the same canonicalisation to the parser AST so the rendered
    // rule body matches HS byte-for-byte.  `term_to_lnterm` covers the
    // LNTerm path; this call is the parser-AST path's equivalent.
    use crate::elaborate::canonicalize_ac_in_pfact;
    let prems2: Vec<p::Fact> = prems.iter().map(canonicalize_ac_in_pfact).collect();
    let acts2: Vec<p::Fact> = acts.iter().map(canonicalize_ac_in_pfact).collect();
    let concs2: Vec<p::Fact> = concs.iter().map(canonicalize_ac_in_pfact).collect();
    render_rule_body_at(&prems2, &acts2, &concs2, 3)
}

/// Render rule body at column `indent`.  Used by the AC variant block
/// (via `render_rule_body`, which prepends 2 spaces) and the top-level
/// rule (indent=3).
///
/// HS `prettyNamedRule` wraps the body as `nest 2 (prettyRule ...)`
/// (Theory/Model/Rule.hs:1397-1400), and `prettyRuleRestrGen`
/// (Model/Rule.hs:1366-1383) lays out `sep [nest 1 (ppFactsList prems), arrow,
/// nest 1 (ppFactsList concls)]`.  The combined `nest 2 + nest 1` puts
/// the bracket `[` at col 3, the arrow at col 2.  We build the whole body
/// as one `pretty_hpj::Doc` (`rule_body_to_doc`) nested by `indent - 1`
/// (== 2 for indent=3) so the HughesPJ engine makes the `sep`/`fsep`
/// wrap decisions byte-identically to HS, instead of the hand-rolled
/// string packers.
fn render_rule_body_at(
    prems: &[p::Fact],
    acts: &[p::Fact],
    concs: &[p::Fact],
    indent: usize,
) -> String {
    let nest = indent.saturating_sub(1) as isize;
    pf::rule_body_to_doc(prems, acts, concs).nest(nest).render()
}

/// Render the HS `/* rule (modulo AC) <name>: ... variants (modulo AC)
/// 1. ... */` comment block.  Mirrors `prettyClosedProtoRule`'s
/// `multiComment $ prettyProtoRuleAC ruAC` branch (ClosedTheory.hs:332-366, see line 354).
///
/// HS `prettyProtoRuleACInfo` (Theory/Model/Rule.hs:1407-1413) emits the variants
/// sub-block via `ppVariants`, which returns `emptyDoc` when the
/// disjunction is exactly `[emptySubstVFresh]`.  So when RS's
/// `variant_substs` is empty (== HS's `[empty]`) or every subst is
/// itself empty, we emit only the rule body — no `variants (modulo AC)`
/// header — matching HS byte-for-byte for the AddPublicKey-style case
/// where the AC body differs from the E body but no residual variant
/// disjunction remains.
fn render_ac_variants_block(
    name: &str,
    rule: &crate::theory::OpenProtoRule,
    attrs: &[p::RuleAttr],
) -> String {
    use crate::pretty_hpj::{hl_close, hl_open, Hl};
    let mut s = String::new();
    // HS `nest 2 (multiComment (prettyProtoRuleAC ruAC))` (ClosedTheory.hs:332-366, see line 354):
    // `multiComment = comment (fsep [text "/*", …, text "*/"])` wraps the whole
    // `/* … */` in an `hl_comment` span (opened after the 2-space indent).
    s.push_str("  ");
    s.push_str(&hl_open(Hl::Comment));
    s.push_str("/*\n");
    // HS renders the AC rule via `nest 2 (multiComment (prettyProtoRuleAC …))`
    // (ClosedTheory.hs:332-366, see line 354), so the `rule (modulo AC) <name>[attrs]:` header
    // line sits at column 2 and its attribute-list `fsep` wraps at the ribbon
    // width with the continuation hanging right after the `[`.  Build it through
    // the same Doc engine as the modulo-E header, prefixed by the 2-space
    // comment indent so the absolute columns (and thus the wrap point) match HS.
    {
        use crate::pretty_hpj::Doc;
        // Build the header with NO leading spaces, then `nest(2)` so BOTH the
        // first line and the `fsep` continuation are indented exactly like HS's
        // `nest 2 (multiComment …)` — the ribbon/width accounting is measured
        // from the nest-2 baseline (a literal 2-space text prefix would charge
        // the first line differently and wrap one element too early; cf.
        // no-replication.spthy `news_0_`).
        let header = crate::pretty_hpj::kw_rule_modulo("AC")
            .beside_sp(Doc::text(name))
            .beside(rule_attributes_doc(attrs))
            .beside(Doc::text(":"))
            .nest(2);
        s.push_str(&header.render());
        s.push('\n');
    }
    // Body of the abstracted rule.  Use the abstracted rule's facts when
    // available; when `abstracted_rule` is `None` (no reducible-headed
    // sub-terms), fall back to the ELABORATED rule's facts (`rule.rule`).
    // This is the macro case: the elaborated facts have macro calls expanded
    // (e.g. `aenc(~k, pkS)` instead of `encrypt(~k, pkS)`) — exactly what HS's
    // `cprRuleAC` holds after `variantsProtoRule (applyMacroInRule macros ruE)`.
    let ac_rule = rule.abstracted_rule.as_ref().unwrap_or(&rule.rule);
    let prems = lnfacts_to_parser(&ac_rule.premises);
    let acts = lnfacts_to_parser(&ac_rule.actions);
    let concs = lnfacts_to_parser(&ac_rule.conclusions);
    // The comment block sits inside HS's `nest 2 (multiComment
    // (prettyNamedRule …))` (ClosedTheory.hs:332-366, see line 354), so the rule body's
    // facts land at absolute column 5 (2 comment + 2 rule nest + 1
    // bracket).  CRITICAL: render the body with the ENGINE aware of the
    // full indent (nest 4 via indent=5) — the HughesPJ width decisions must
    // be made at the absolute column, so lines within 2 columns of the
    // boundary break exactly where HS breaks (cf. the spdm R_KE_Response
    // tuple: HS breaks at col 95).
    use crate::elaborate::canonicalize_ac_in_pfact;
    let prems2: Vec<p::Fact> = prems.iter().map(canonicalize_ac_in_pfact).collect();
    let acts2: Vec<p::Fact> = acts.iter().map(canonicalize_ac_in_pfact).collect();
    let concs2: Vec<p::Fact> = concs.iter().map(canonicalize_ac_in_pfact).collect();
    let body = render_rule_body_at(&prems2, &acts2, &concs2, 5);
    s.push_str(&body);
    if !body.ends_with('\n') {
        s.push('\n');
    }
    // HS `ppVariants (Disj [subst]) | subst == emptySubstVFresh = emptyDoc`
    // (Theory/Model/Rule.hs:1407-1413, see line 1412): skip the variants sub-block when there's no
    // residual disjunction beyond the identity.
    let has_residual_variants = rule.variant_substs.iter().any(|sub| !sub.is_empty());
    if has_residual_variants {
        // HS `kwVariantsModulo "AC"` = `kwModulo "variants" "AC"` =
        // `keyword_ "variants" <-> parens (keyword_ "modulo" <-> text "AC")`.
        s.push_str("    ");
        s.push_str(&crate::pretty_hpj::kw_modulo("variants", "AC").render());
        s.push('\n');
        // HS `prettyDisjLNSubstsVFresh = numbered' (map ppConj substs)`
        // (SubstVFresh.hs:223-227).  Built and rendered as ONE Doc at
        // `nest 4` so the `text i <> ". " <> vcat` beside-onto-multiline
        // ribbon interaction is HS-faithful — see `variant_subst_doc`.
        s.push_str(&render_variant_substs_block(&rule.variant_substs));
    }
    // HS `prettyProtoRuleACInfo i = ppVariants ... $-$ prettyLoopBreakers i`
    // (Theory/Model/Rule.hs:1407-1410): the loop-breaker line also appears INSIDE the
    // `multiComment` AC block, at the same nest-2 column as the rule
    // body (= absolute column 4 here, since the outer block is itself
    // at indent 2 inside `nest 2 (multiComment ...)`).
    s.push_str(&render_loop_breakers_line(&rule.loop_breakers, 4));
    s.push_str("  */");
    s.push_str(&hl_close(Hl::Comment));
    s
}

/// Render one entry of `prettyDisjLNSubstsVFresh` (SubstVFresh.hs:223-229)
/// as a Doc: the variant's number, then each domain var followed by
/// `= <range>`.  `n_width` is the width of the largest variant number
/// (HS `numbered`'s `nWidth = length (show n)`,
/// Text/PrettyPrint/Class.hs:252-259, see line 258); each
/// variant's number is right-flushed in that width so dots line up.
///
/// HS `numbered` (Text/PrettyPrint/Class.hs:252-259) renders each variant as
/// `pp (i, d) = text (flushRight nWidth (show i)) <> d` where `d` is
/// `text ". " <> vcat (map prettyEq bindings)`.  The whole `numbered'`
/// block sits at `nest 4` inside the rule's `multiComment`.
///
/// CRITICAL: the `text ". " <>` is a BESIDE onto the multi-line `vcat`.
/// In HughesPJ the ribbon budget for the inner (wrapped) lines is then
/// measured from the OUTER line start (the `text i` column), not from the
/// var column.  So build the whole numbered conjunction as ONE Doc and
/// render it at `nest 4` (do NOT render each binding STANDALONE via
/// `entry.nest(col)` — that measures the ribbon from the var column and
/// shifts wrap decisions for terms within a few columns of the boundary,
/// e.g. an 11-tuple `<x.16, …, x.26>`: pkcs11-templates
/// `cannot_obtain_key` et al.), mirroring HS byte-for-byte.
fn variant_subst_doc(
    n: usize,
    subst: &tamarin_term::subst_vfresh::LNSubstVFresh,
    n_width: usize,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let bindings = subst.to_list();
    // HS `prettyEq (a,b) = prettyNTerm (Var a) $$ nest 6 (text "="
    // <-> prettyNTerm b)` (SubstVFresh.hs:228-229).  `<->` is `<+>`
    // (beside-with-space).
    let eq_docs: Vec<Doc> = bindings
        .iter()
        .map(|(v, t)| {
            let term_doc = pf::term_to_doc(&lnterm_to_parser(t), &[]);
            // HS `prettyEq (a,b) = prettyNTerm (Var a) $$ nest 6 (text "=" <->
            // prettyNTerm b)` (SubstVFresh.hs:228-229) — the substitution `=` is a
            // PLAIN `text`, NOT `opEqual`, so it carries no `hl_operator` span.
            let rhs = Doc::text("=").beside_sp(term_doc).nest(6);
            Doc::text(render_lvar(v)).above(rhs)
        })
        .collect();
    let conj = hpj::vcat(eq_docs);
    // HS `pp (i, d) = text (flushRight nWidth (show i)) <> d`, with
    // `d = text ". " <> conj` (from `numbered' = numbered (text "")
    // . map (text ". " <>)`).
    let label = format!("{:>width$}", n, width = n_width);
    Doc::text(label).beside(Doc::text(". ").beside(conj))
}

/// Render the full `prettyDisjLNSubstsVFresh` (numbered') block.  HS
/// `numbered vsep ds = foldr1 ($-$) $ intersperse vsep $ map pp ...` with
/// `vsep = text ""` (a blank separator line at the block's nest).
///
/// Each numbered conjunction is an independent Doc rendered at `nest 4`
/// (the `multiComment` indent) — they don't interact across the blank
/// separators, so rendering them individually is faithful — and joined by
/// the blank `"    \n"` line (HS `text ""` at nest 4).  Building each
/// conjunction as a single Doc (not per-binding) is what reproduces the
/// `text i <> ". " <> vcat` beside-onto-multiline ribbon decision.
fn render_variant_substs_block(substs: &[tamarin_term::subst_vfresh::LNSubstVFresh]) -> String {
    let n_width = substs.len().to_string().len();
    let mut s = String::new();
    for (i, subst) in substs.iter().enumerate() {
        if i > 0 {
            // HS `intersperse (text "")` → a blank line at nest 4.
            s.push_str("    \n");
        }
        let mut rendered = variant_subst_doc(i + 1, subst, n_width).nest(4).render();
        rendered.push('\n');
        s.push_str(&rendered);
    }
    s
}

/// Render a `LVar` the way HS `instance Show LVar` (LTerm.hs:550-557) does:
/// sort prefix (`~`/`$`/`#`/`%`/empty), then the root name, then `.idx` when
/// `idx /= 0`.  Delegates to [`tamarin_term::pretty::pp_lvar`], the HS-faithful
/// mirror, so the empty-name branch matches HS exactly.
fn render_lvar(v: &tamarin_term::lterm::LVar) -> String {
    let mut s = String::new();
    tamarin_term::pretty::pp_lvar(v, &mut s);
    s
}

/// Render a timepoint / node id from a (root-name, idx) pair the way HS's
/// `Show LVar` (Node sort) does: `#name` for idx 0, else `#name.idx`.
/// Mirrors [`render_lvar`] for a `LSort::Node` var without constructing one;
/// used by `raw_goal_to_doc` to re-render an unannotated goal head with its
/// timepoint index preserved (HS `prettyGoal`'s `show i`).
fn render_node_id_str(name: &str, idx: u32) -> String {
    if idx == 0 {
        format!("#{}", name)
    } else {
        format!("#{}.{}", name, idx)
    }
}

/// Convert LNFacts (post-elaboration) to parser-AST Facts so we can
/// reuse the parser-AST fact rendering path.
pub(crate) fn lnfacts_to_parser(facts: &[crate::fact::LNFact]) -> Vec<p::Fact> {
    facts.iter().map(lnfact_to_parser).collect()
}

/// Materialise an elaborated `ProtoRuleE` as a parser-AST rule item, so a
/// synthesised rule (SAPIC translation, partial evaluation) can join the
/// parsed-item stream `pretty_closed_theory` renders from — the display facts
/// come from here.
///
/// The body is the elaborated E-rule projected back through
/// [`lnfacts_to_parser`], so it is already macro/let expanded: the render
/// path's `apply_let_block` / macro checks are no-ops, and AC argument order
/// is canonicalised at render time (`render_rule_body`), exactly as for the
/// modulo-AC comment blocks.  The attributes carry color / process /
/// no_derivcheck / issapicrule / role, as HS's `toRule` produced them.
pub fn proto_rule_to_parsed(r: &crate::rule::ProtoRuleE) -> p::Rule {
    p::Rule {
        name: match &r.info.name {
            crate::rule::ProtoRuleName::Stand(s) => s.to_string(),
            crate::rule::ProtoRuleName::Fresh => "Fresh".to_string(),
        },
        modulo: None,
        attributes: crate::mult_restricted::surface_attrs(&r.info.attributes),
        let_block: Vec::new(),
        premises: lnfacts_to_parser(&r.premises),
        actions: lnfacts_to_parser(&r.actions),
        conclusions: lnfacts_to_parser(&r.conclusions),
        embedded_restrictions: Vec::new(),
        variants: Vec::new(),
        left_right: None,
    }
}

pub fn lnfact_to_parser(fa: &crate::fact::LNFact) -> p::Fact {
    use crate::fact::FactTag;
    let (name, persistent) = match &fa.tag {
        FactTag::Proto(crate::fact::Multiplicity::Persistent, n, _) => (n.to_string(), true),
        FactTag::Proto(_, n, _) => (n.to_string(), false),
        FactTag::Fresh => ("Fr".to_string(), false),
        FactTag::In => ("In".to_string(), false),
        FactTag::Out => ("Out".to_string(), false),
        // KU and KD are Persistent per factTagMultiplicity (Model/Fact.hs:358-359).
        FactTag::Ku => ("KU".to_string(), true),
        FactTag::Kd => ("KD".to_string(), true),
        FactTag::Ded => ("Ded".to_string(), false),
        FactTag::Term => ("Term".to_string(), false),
    };
    p::Fact {
        persistent,
        name,
        args: fa.terms.iter().map(lnterm_to_parser).collect(),
        // HS `prettyFact` appends `ppAnn an` to every fact (Theory/Model/Fact.hs:567-574),
        // so the annotations must survive the projection.  `fa.annotations`
        // is a `BTreeSet<FactAnnotation>` whose iteration order IS the HS
        // `S.toList` (Ord) order the renderer expects.
        annotations: fa
            .annotations
            .iter()
            .map(|a| match a {
                crate::fact::FactAnnotation::SolveFirst => p::FactAnnotation::SolveFirst,
                crate::fact::FactAnnotation::SolveLast => p::FactAnnotation::SolveLast,
                crate::fact::FactAnnotation::NoSources => p::FactAnnotation::NoSources,
            })
            .collect(),
    }
}

/// `Atom<LNTerm>` → parser-AST `Atom`: [`lnterm_to_parser`] and
/// [`lnfact_to_parser`] over the arms of HS `Atom` (Atom.hs:78-84,100), the
/// atom-level twin of [`lnfact_to_parser`].
///
/// A `Syntactic` atom has no parser-AST form here: HS's `Unit2` sugar carries
/// no fact (Atom.hs:92-94), and [`crate::formula::to_lnformula`] refuses an
/// atom that still holds sugar, so an `LNFormula` holds none.
pub fn lnatom_to_parser(a: &crate::atom::Atom<tamarin_term::lterm::LNTerm>) -> p::Atom {
    use crate::atom::ProtoAtom;
    match a {
        ProtoAtom::Action(t, fa) => p::Atom::Action(lnfact_to_parser(fa), lnterm_to_parser(t)),
        ProtoAtom::EqE(l, r) => p::Atom::Eq(lnterm_to_parser(l), lnterm_to_parser(r)),
        ProtoAtom::Subterm(l, r) => p::Atom::Subterm(lnterm_to_parser(l), lnterm_to_parser(r)),
        ProtoAtom::Less(l, r) => p::Atom::Less(lnterm_to_parser(l), lnterm_to_parser(r)),
        ProtoAtom::Last(t) => p::Atom::Last(lnterm_to_parser(t)),
        ProtoAtom::Syntactic(crate::atom::Unit2) => {
            panic!("lnatom_to_parser: syntactic sugar in a plain atom")
        }
    }
}

/// `LNTerm` → parser-AST `Term`: the projection every printer of an `LNTerm`
/// goes through, and the term-level twin of [`lnfact_to_parser`].
///
/// The parser AST is the universe HS `prettyTerm` (Term/Term.hs:299-317) prints
/// from, so the shapes that function special-cases must be materialised here:
/// `exp` as the infix `^` (line 310), a `pair` chain as the n-ary tuple its
/// `split` walks out of the RIGHT spine (lines 313,323-324), an AC symbol as
/// the infix chain of its `ppTerms` arms (lines 305-309), a nullary user-`[AC]`
/// symbol as its bare name (line 304) and `List` as `LIST(…)` (line 317).
///
/// `tamarin-sapic` lowers through this same function (its restriction and
/// `if`-predicate bodies are parser-AST formulas), so the two surfaces cannot
/// disagree about any of those shapes.
pub fn lnterm_to_parser(t: &tamarin_term::lterm::LNTerm) -> p::Term {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => p::Term::Var(p::VarSpec {
            name: v.name.to_string(),
            idx: v.idx,
            sort: v.sort,
            typ: None,
        }),
        Term::Lit(Lit::Con(n)) => {
            use tamarin_term::lterm::NameTag;
            match n.tag {
                NameTag::Pub => p::Term::PubLit(n.id.0.to_string()),
                NameTag::Fresh => p::Term::FreshLit(n.id.0.to_string()),
                NameTag::Nat => p::Term::NatLit(n.id.0.to_string()),
                NameTag::Node => p::Term::PubLit(n.id.0.to_string()),
                // `prettyTerm`'s literal case is `text . show`, and `show
                // (Name AbbrevName n) = show n` (LTerm.hs:240) is the bare id;
                // a nullary `App` is the parser-AST term `pp_term` renders
                // that way.  Reached from `prettyLNFact` on the facts
                // `Web.Utils.abbrev` rewrote.
                NameTag::Abbrev => p::Term::App(n.id.0.to_string(), Vec::new()),
            }
        }
        Term::App(FunSym::NoEq(sym), args) => {
            let name = String::from_utf8_lossy(sym.name).to_string();
            // `exp` is the DH exponentiation infix operator — HS
            // `prettyTerm` (Term/Term.hs:310) renders `exp(a, b)` as `a^b`.
            // Surface as `p::Term::BinOp(Exp, ..)` so `pp_term`'s special
            // case applies.
            if name == "exp" && args.len() == 2 {
                return p::Term::BinOp(
                    p::BinOp::Exp,
                    Box::new(lnterm_to_parser(&args[0])),
                    Box::new(lnterm_to_parser(&args[1])),
                );
            }
            // A `pair` chain flattens to the n-ary tuple HS `prettyTerm`'s
            // `split` produces (Term/Term.hs:313,323-324): `split` consumes the
            // RIGHT child while it is itself a pair, so a left-nested
            // `pair(pair(a,b),c)` stays the 2-tuple `<<a, b>, c>`.
            if name == "pair" && args.len() == 2 {
                let mut items: Vec<p::Term> = Vec::new();
                items.push(lnterm_to_parser(&args[0]));
                let mut tail = &args[1];
                loop {
                    match tail {
                        Term::App(FunSym::NoEq(s2), a2)
                            if a2.len() == 2 && String::from_utf8_lossy(s2.name) == "pair" =>
                        {
                            items.push(lnterm_to_parser(&a2[0]));
                            tail = &a2[1];
                        }
                        _ => {
                            items.push(lnterm_to_parser(tail));
                            break;
                        }
                    }
                }
                return p::Term::Pair(items);
            }
            p::Term::App(name, args.iter().map(lnterm_to_parser).collect())
        }
        // HS `FApp (C EMap) ts -> ppFun emapSymString ts` (Term/Term.hs:316).
        Term::App(FunSym::C(_), args) => p::Term::App(
            "em".to_string(),
            args.iter().map(lnterm_to_parser).collect(),
        ),
        // HS `prettyTerm` (Term/Term.hs:304): `FApp (AC (ACfct (f,_))) [] ->
        // text (BC.unpack f)` — a nullary user-AC symbol is the bare name,
        // which `term_to_doc` renders for a nullary `App`.
        Term::App(FunSym::Ac(AcSym::AcFct(s)), args) if args.is_empty() => {
            p::Term::App(String::from_utf8_lossy(s.name).into_owned(), vec![])
        }
        Term::App(FunSym::Ac(ac), args) => {
            // Render AC as left-assoc binops to preserve display.
            let op = match ac {
                AcSym::Mult => p::BinOp::Mult,
                AcSym::Union => p::BinOp::Union,
                AcSym::NatPlus => p::BinOp::NatPlus,
                AcSym::Xor => p::BinOp::Xor,
                // HS renders a user-declared `[AC]` symbol INFIX too
                // (Term/Term.hs:305): `ppTerms (" " ++ BC.unpack f ++ " ") 1
                // "(" ")" ts`, i.e. `(x add y)`.
                AcSym::AcFct(s) => p::BinOp::AcFct(tamarin_term::intern::intern_str(
                    &String::from_utf8_lossy(s.name),
                )),
            };
            let mut it = args.iter();
            let first = lnterm_to_parser(it.next().expect("AC needs at least one arg"));
            it.fold(first, |acc, next| {
                p::Term::BinOp(op, Box::new(acc), Box::new(lnterm_to_parser(next)))
            })
        }
        // HS `FApp List ts -> ppFun "LIST" ts` (Term/Term.hs:317).
        Term::App(FunSym::List, args) => p::Term::App(
            "LIST".to_string(),
            args.iter().map(lnterm_to_parser).collect(),
        ),
    }
}

/// HughesPJ default-`style` line length used by the oracle/tactic
/// ranking path.  HS `render = P.render` (`Text.PrettyPrint.Class`
/// re-exports `P.render` from HughesPJ — Text/PrettyPrint/Class.hs:77-78), and `P.render`
/// uses HughesPJ's default `style { lineLength = 100 }`.  This is
/// DISTINCT from the `--prove` DISPLAY width (`pretty_hpj::LINE_LENGTH`
/// = 110, set by `defaultStyle { lineLength = lineWidth }` in
/// Console.hs:242-243,398-399).
const ORACLE_LINE_LENGTH: usize = 100;

/// HughesPJ default-`style` ribbon length used by the oracle/tactic
/// path: `ribbonsPerLine = 1.5` → `round(100/1.5) = round(66.67) = 67`.
/// DISTINCT from the display ribbon `pretty_hpj::RIBBON` = 73.
const ORACLE_RIBBON: usize = 67;

// =============================================================================
// Lemma
// =============================================================================

/// HS `prettyLemma` (lib/theory/src/Lemma.hs:116-141) over the ELABORATED
/// lemma the parsed item names.  `_lFormula` is the macro- and
/// predicate-expanded formula elaboration stored and `_lOriginalFormula` the
/// pre-macro one, so the header line quotes `fromMaybe expandedFormula
/// ogFormula` (lib/theory/src/Lemma.hs:121) and the guarded block converts
/// `_lFormula` (lib/theory/src/Lemma.hs:125).  The name and the attributes
/// come from the parsed item, which is what the printer walks.  A parsed
/// lemma with no elaborated twin renders nothing, as an unpaired rule does.
fn render_parsed_lemma(
    lem: &p::Lemma,
    proved: &[ProvedLemma],
    in_file: &str,
    elab: &Theory,
) -> Option<String> {
    let el = elab.lookup_lemma(&lem.name)?;
    let original = el.original_formula.as_ref().unwrap_or(&el.formula);
    let mut out = render_lemma_head(
        lem,
        in_file,
        pf::lnformula_doc(original),
        &render_guarded_block(el),
    );

    // Proof body — either the prover's result (if --prove ran) or
    // the lemma's stored skeleton.
    let proof = proved.iter().find(|p| p.name == lem.name);
    let body = match proof.and_then(|p| p.proof_body.as_ref()) {
        Some(b) => b.clone(),
        None => "by sorry".to_string(),
    };
    out.push('\n');
    out.push_str(&body);
    Some(out)
}

/// Everything of HS `prettyLemma` (lib/theory/src/Lemma.hs:116-141) BEFORE the proof body:
/// the `lemma <name> [attrs]:` header, the `<quant> "<formula>"` line, and
/// the `/* guarded formula ... */` comment block.  The name, the attributes
/// and the trace quantifier come from the parsed item; `formula_doc` is the
/// quoted formula of the quantifier line and `guarded_block` the comment,
/// both built by the caller from the formula representation it holds.
/// Shared by the closed renderer (`render_parsed_lemma`, which appends the
/// prover's proof body) and the open `--parse-only` renderer
/// (`render_open_lemma`, which appends the parsed proof skeleton).
fn render_lemma_head(
    lem: &p::Lemma,
    in_file: &str,
    formula_doc: crate::pretty_hpj::Doc,
    guarded_block: &str,
) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    let mut out = String::new();
    // HS `prettyLemmaName` (lib/theory/src/Lemma.hs:91-95):
    //   `text name <-> brackets (fsep (punctuate comma attrs))`
    // The whole header line is:
    //   `kwLemma <-> prettyLemmaName lem <> colon`
    // Rendered via HughesPJ so `fsep` wraps the attributes list when the
    // line is long (e.g. `[heuristic={…}, use_induction,\n<col>reuse]`).
    let kw = Doc::text("lemma");
    let name_doc = Doc::text(lem.name.clone());
    let header_doc = if lem.attributes.is_empty() {
        kw.beside_sp(name_doc).beside(Doc::text(":"))
    } else {
        let attr_docs: Vec<Doc> = lemma_attr_docs(&lem.attributes, in_file);
        // `brackets (fsep (punctuate comma attrs))` — no space after `[`
        // (beside, not beside_sp) so fsep's continuation aligns with the
        // first attr character (i.e. right after `[`).
        let attrs_fsep = hpj::fsep(hpj::punctuate(Doc::text(","), attr_docs));
        let brackets = Doc::text("[").beside(attrs_fsep).beside(Doc::text("]"));
        kw.beside_sp(name_doc)
            .beside_sp(brackets)
            .beside(Doc::text(":"))
    };
    out.push_str(&header_doc.render());
    out.push('\n');

    // Lemma body shape from HS `prettyLemma` (lib/theory/src/Lemma.hs:119-122):
    //   `nest 2 $ sep [ prettyTraceQuantifier, doubleQuotes (prettyLNFormula f) ]`
    // Routed through the HS-faithful Doc engine so the quant-vs-formula
    // `sep` wrap, the formula's internal `sep`/`nest` wrapping, and the
    // continuation indents are byte-identical to HS.  The `nest 2` indent
    // is included in the rendered output (HS renders it at theory col 0).
    let quant = quantifier_keyword(&lem.trace_quantifier);
    out.push_str(&pf::lemma_header_line_doc(quant, formula_doc));
    out.push('\n');

    // /* guarded formula characterizing ... */
    out.push_str(guarded_block);
    out
}

/// Build `Doc` nodes for each lemma attribute.  Mirrors HS
/// `prettyLemmaAttribute` (lib/theory/src/Lemma.hs:97-107): each attribute becomes a
/// `text "..."` Doc; these are assembled into
/// `brackets (fsep (punctuate comma docs))` by the caller.
fn lemma_attr_docs(attrs: &[p::LemmaAttr], in_file: &str) -> Vec<crate::pretty_hpj::Doc> {
    use crate::pretty_hpj::Doc;
    let mut out = Vec::new();
    for a in attrs {
        use p::LemmaAttr::*;
        let s: Option<String> = match a {
            Sources => Some("sources".into()),
            Reuse => Some("reuse".into()),
            DiffReuse => Some("diff_reuse".into()),
            UseInduction => Some("use_induction".into()),
            HideLemma(s) => Some(format!("hide_lemma={}", s)),
            // HS `prettyLemmaAttribute (LemmaHeuristic h)`
            // (lib/theory/src/Lemma.hs:97-107, see line 103):
            //   `text ("heuristic=" ++ prettyGoalRankings h)`
            // Mirror space-separated, oracle-name-expanded rendering.
            Heuristic(s) => Some(format!("heuristic={}", pretty_goal_rankings(s, in_file))),
            Output(modules) => Some(format!("output=[{}]", modules.join(","))),
            Left => Some("left".into()),
            Right => Some("right".into()),
            _ => None,
        };
        if let Some(s) = s {
            out.push(Doc::text(s));
        }
    }
    out
}

fn quantifier_keyword(q: &p::TraceQuantifier) -> &'static str {
    match q {
        p::TraceQuantifier::AllTraces => "all-traces",
        p::TraceQuantifier::ExistsTrace => "exists-trace",
    }
}

/// HS `ppLNFormulaGuarded` (lib/theory/src/Lemma.hs:131-141) over the
/// ELABORATED lemma's `_lFormula`.
fn render_guarded_block(lem: &crate::theory::Lemma) -> String {
    guarded_block_comment(
        matches!(
            lem.trace_quantifier,
            crate::theory::TraceQuantifier::ExistsTrace
        ),
        crate::guarded::formula_to_guarded(&lem.formula),
        || crate::pretty_formula::pretty_lnformula(&lem.formula),
    )
}

/// [`render_guarded_block`] for the `--parse-only` renderer, over the parsed
/// lemma's surface formula.  The parse-time lemma's guarded characterization
/// is computed BEFORE `applyMacroInLemma` runs, so no macro is applied here —
/// oracle-verified: `--parse-only` prints `m1('a')` un-expanded inside the
/// guarded block where the closed print shows `h('a')`.  HS `expandLemma`
/// (TheoryObject.hs:439-446) does predicate-expand at parse, and the arity-1
/// surplus-argument fold (`naryOpApp` `k == 1`, Parser/Term.hs:94-96) happens
/// in the term parser, so the guarded form carries `h(<…>)` not `h(…)`.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_open_guarded_block(
    lem: &p::Lemma,
    predicates: &[p::Predicate],
    arity1: &std::collections::HashSet<String>,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> String {
    let expanded_formula = crate::elaborate::rewrite_arity1_formula(
        &expand_predicates_for_display(&lem.formula, predicates),
        arity1,
    );
    guarded_block_comment(
        matches!(lem.trace_quantifier, p::TraceQuantifier::ExistsTrace),
        crate::guarded::formula_to_guarded_parsed(&expanded_formula, msig),
        || crate::pretty_formula::pretty_formula(&expanded_formula),
    )
}

/// The `/* guarded formula characterizing ... */` comment of HS
/// `ppLNFormulaGuarded` (lib/theory/src/Lemma.hs:131-141) around an already
/// converted formula.  `full_text` writes the quoted whole formula of the
/// failure branch, which the success branch never needs.
fn guarded_block_comment(
    exists_trace: bool,
    gf: Result<crate::guarded::Guarded, crate::guarded::GuardError>,
    full_text: impl FnOnce() -> String,
) -> String {
    let header = if exists_trace {
        "guarded formula characterizing all satisfying traces:"
    } else {
        "guarded formula characterizing all counter-examples:"
    };
    let gf = match gf {
        Ok(g) => g,
        Err(e) => {
            // HS lib/theory/src/Lemma.hs:132-134: `multiComment (text "conversion to
            // guarded formula failed:" $$ nest 2 err)` where `err` is the
            // full `ppError` doc (Guarded.hs:471-566, see line 479): the error text, the
            // quoted failing sub-formula (Guarded.hs:508-514/561-563 both
            // include `ppFormula f0`), then "in the formula" + the quoted
            // formula passed to `formulaToGuarded` (nest 2 . doubleQuotes).
            let mut block = String::from("/*\nconversion to guarded formula failed:\n");
            for line in e.message.lines() {
                block.push_str("  ");
                block.push_str(line);
                block.push('\n');
            }
            let full_text = full_text();
            let sub_text = e
                .subject_formula
                .as_ref()
                .map(crate::pretty_formula::pretty_lnformula)
                .unwrap_or_else(|| full_text.clone());
            block.push_str("    \"");
            block.push_str(&sub_text);
            block.push_str("\"\n  in the formula\n    \"");
            block.push_str(&full_text);
            block.push_str("\"\n*/");
            return block;
        }
    };
    // For all-traces lemmas, HS prints the negated guarded formula
    // (`gnot gf`).  The result is the "counter-example" form.
    //
    // The guarded block is rendered inside `multiComment` at col 0 with
    // the formula wrapped in `doubleQuotes` (HS lib/theory/src/Lemma.hs:116-141, see line 138/141:
    // `doubleQuotes (prettyGuarded gf)`).  `pretty_guarded_doublequoted`
    // models the `"` as a real `Doc` `beside`, so HughesPJ's column-shift
    // puts continuation lines at the formula's start column (1) — exactly
    // like HS's `"\"" <> prettyGuarded <> "\""`.
    let to_render = if exists_trace {
        gf
    } else {
        crate::guarded::gnot(&gf)
    };
    let quoted = pf::pretty_guarded_doublequoted(&to_render);
    format!("/*\n{}\n{}\n*/", header, quoted)
}

// =============================================================================
// Restriction
// =============================================================================

/// Predicate-expand a formula for DISPLAY, mirroring HS `expandFormula`
/// (Theory/Syntactic/Predicate.hs:82-93) as applied by `expandRestriction` /
/// `expandLemma` (TheoryObject.hs:430-446).  This rewrites `Pred` sugar — and
/// the builtin multiset `(<)` / `Smaller` — into the surviving atom forms, so
/// the displayed lemma/restriction text matches HS byte-for-byte.  The parse
/// already succeeded (so every referenced predicate is defined and arities
/// match); should expansion nonetheless error, fall back to the un-expanded
/// formula rather than panic.
pub(crate) fn expand_predicates_for_display(
    f: &p::Formula,
    predicates: &[p::Predicate],
) -> p::Formula {
    crate::predicate_expand::expand_formula(f, predicates).unwrap_or_else(|_| f.clone())
}

/// HS `prettyRestriction` (TheoryObject.hs:889-901) over the ELABORATED
/// restriction the parsed item names.  `_rstrFormula` is the macro- and
/// predicate-expanded formula elaboration stored and `_rstrOriginalFormula`
/// the pre-macro one, so the body shows `fromMaybe expandedFormula ogFormula`
/// (TheoryObject.hs:893), the safety predicate runs on `_rstrFormula`
/// (TheoryObject.hs:901) and the `expanded formula:` comment shows
/// `_rstrFormula` (TheoryObject.hs:895-898).  That block sits under
/// `case ogFormula of Just _`, and elaboration and the SAPIC injection both
/// fill `original_formula`, so it is always written.  The name and the
/// `left`/`right` attributes come from the parsed item, which is what the
/// printer walks.  A parsed restriction with no elaborated twin renders
/// nothing, as an unpaired rule does.
fn render_parsed_restriction(r: &p::Restriction, elab: &Theory) -> Option<String> {
    let er = elab.lookup_restriction(&r.name)?;
    let original = er.original_formula.as_ref().unwrap_or(&er.formula);
    use crate::pretty_hpj::{
        escape_html_entities, hl_close, hl_open, html_mode, keyword_, line_comment_, Hl,
    };
    let mut out = String::new();
    // HS `kwRestriction <-> text name <> colon` (TheoryObject.hs:891-892):
    // `restriction` is a keyword; the name is `text` (entity-escaped in HtmlDoc
    // mode).  `keyword_`/escaping are identities in plain mode.
    out.push_str(&keyword_("restriction").render());
    out.push(' ');
    if html_mode() {
        out.push_str(&escape_html_entities(&r.name));
    } else {
        out.push_str(&r.name);
    }
    render_restriction_attributes(&r.attributes, &mut out);

    out.push_str(":\n");
    out.push_str(&pf::doublequoted_nested_doc(pf::lnformula_doc(original), 2));
    // `nest 2 (if safety then lineComment_ "safety formula" else emptyDoc)`
    // (TheoryObject.hs:894).
    if is_safety_formula(&er.formula) {
        out.push_str("\n  ");
        out.push_str(&line_comment_("safety formula").render());
    }
    // `nest 2 (multiComment (text "expanded formula:" $-$ doubleQuotes
    // (prettyLNFormula expandedFormula)))` (TheoryObject.hs:896-897).
    // `multiComment = comment (…)` wraps the whole `/* … */` in an
    // `hl_comment` span; the inner formula still carries its own operator spans.
    out.push_str("\n\n  ");
    out.push_str(&hl_open(Hl::Comment));
    out.push_str("/*\n  expanded formula:\n");
    out.push_str(&pf::doublequoted_nested_doc(
        pf::lnformula_doc(&er.formula),
        2,
    ));
    out.push_str("\n  */");
    out.push_str(&hl_close(Hl::Comment));
    Some(out)
}

/// Render the restriction attributes, i.e., `left` and/or `right`
fn render_restriction_attributes(attrs: &[p::RestrictionAttr], out: &mut String) {
    if attrs.is_empty() {
        return;
    }
    out.push(' ');
    out.push('[');
    let attr_strs: Vec<&str> = attrs
        .iter()
        .map(|a| match a {
            p::RestrictionAttr::LeftRestriction => "left",
            p::RestrictionAttr::RightRestriction => "right",
        })
        .collect();
    out.push_str(&attr_strs.join(", "));
    out.push(']');
}

/// Render one predicate item, mirroring HS `prettyPredicate`
/// (TheoryObject.hs:845-849):
///   prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
///     factstr    = render $ prettyFact prettyLVar (pFact p)
///     formulastr = render $ prettyLNFormula      (pFormula p)
/// `kwPredicate <> colon` is `predicate:` (no space), `<->` adds one space,
/// then the combined `<fact><=><formula>` text (no spaces around `<=>`).
/// The fact/formula terms are arity-1 folded (HS `naryOpApp` k==1 at parse
/// time), matching the rule/restriction renderers.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn render_predicate(pr: &p::Predicate, arity1: &std::collections::HashSet<String>) -> String {
    use crate::pretty_hpj as hpj;
    let fact = crate::elaborate::rewrite_arity1_fact(&pr.fact, arity1);
    let formula = crate::elaborate::rewrite_arity1_formula(&pr.formula, arity1);
    // `render` is HughesPJ's default style: `lineLength = 100` and
    // `ribbonsPerLine = 1.5`, so `fullRender` rounds the ribbon to 67
    // (HughesPJ.hs:940, :1010) — NOT the 110/73 the console's `renderDoc`
    // installs for the surrounding theory echo.  factstr and formulastr are
    // rendered INDEPENDENTLY at that style from column 0, then concatenated
    // as plain text.
    //
    // Render the predicate fact DIRECTLY (`fact_doc`), NOT via
    // `reparse_fact_doc`.  HS `prettyPredicate` (TheoryObject.hs:845-849) calls
    // `prettyFact prettyLVar (pFact p)`, where each formal-arg `LVar` carries
    // its sort and `prettyLVar` renders the sigil (`#time` for an `LSortNode`
    // arg).  A predicate's args come from the real term parser (`self.term`),
    // so they are proper sorted `Var`s already.  `reparse_fact_doc` is meant
    // for proof-tree facts whose args `build_fact` stuffs into `Var` *names* as
    // raw text; re-parsing a sorted formal arg from its bare `name` drops the
    // sigil (`#time` → `time`).  Going through `fact_doc` preserves the sort.
    let factstr = pf::fact_doc(&fact).render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON);
    let formulastr =
        pf::formula_doc(&formula).render_at(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON, 0);
    format!("predicate: {}<=>{}", factstr, formulastr)
}

/// HS `isSafetyFormula . formulaToGuarded_` (Guarded.hs:156-164 / 466-467) over
/// a restriction's formula.
///
/// `isSafetyFormula gf0 = null (frees [gf0]) && noExistential gf0`
/// (Guarded.hs:157-158): the guarded formula must be CLOSED *and* free of
/// existential quantifiers.  `crate::guarded::is_safety_formula` is that exact
/// predicate; this wrapper supplies the `LNFormula → LNGuarded` step.
/// HS's `formulaToGuarded_` `error`s out when the formula is not guardable
/// (`either (error . render) id`, Guarded.hs:467) and takes the whole run down;
/// an unguardable restriction here yields `false` (no annotation) instead.
fn is_safety_formula(f: &crate::formula::LNFormula) -> bool {
    match crate::guarded::formula_to_guarded(f) {
        Ok(g) => crate::guarded::is_safety_formula(&g),
        Err(_) => false,
    }
}

/// [`is_safety_formula`] on the parser-AST formula the `--parse-only`
/// restriction renderer holds, closed by
/// [`crate::guarded::formula_to_guarded_parsed`].
fn is_safety_formula_parsed(f: &p::Formula, msig: &tamarin_term::maude_sig::MaudeSig) -> bool {
    match crate::guarded::formula_to_guarded_parsed(f, msig) {
        Ok(g) => crate::guarded::is_safety_formula(&g),
        Err(_) => false,
    }
}

// =============================================================================
// Proof body
// =============================================================================

/// Render a proof tree in HS's `prettyProofWith` shape:
///
/// - `Finished Solved` with no children → `SOLVED // trace found`
/// - No children otherwise               → `by <step>` (e.g. `by contradiction`)
/// - One unnamed child                   → `<step>\n<recurse>`
/// - Multiple children                   → `<step>\n  case A\n  ...\nnext\n  case B\n  ...\nqed`
///
/// Mirrors `Theory.Proof.prettyProofWith` (Theory/Proof.hs:1054-1075).
///
/// `sig` supplies the user-declared `[AC]` symbol names an unannotated
/// (replayed) step's stored goal text is re-parsed with.
pub fn pretty_proof_body(
    node: &crate::constraint::solver::search::ProofNode,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> String {
    let mut out = String::new();
    pp_proof(node, &mut out, 0, sig);
    out
}

fn pp_proof(
    node: &crate::constraint::solver::search::ProofNode,
    out: &mut String,
    depth: usize,
    msig: &tamarin_term::maude_sig::MaudeSig,
) {
    use crate::constraint::solver::proof_method::{ProofMethod, Result as MR};
    // The step's first char lands at col `depth*2` (proof body uses
    // 2-space indent per nesting level).
    //
    // HS `prettyIncrementalProof` (ProofSkeleton.hs:80-84) renders each
    // step as `sep [prettyProofMethod, if Nothing then "/* unannotated
    // */" else empty]`.  A step whose constraint system could not be
    // re-attached during the close-time `checkProof` replay
    // (`annotated == false`) gets the `/* unannotated */` comment beside
    // its method.  Fully-searched / successfully-replayed steps stay
    // `Just System` (annotated == true) and render without it.
    // HS `prettyIncrementalProof.ppStep` (ProofSkeleton.hs:80-84) wraps
    // every step as `sep [prettyProofMethod, comment-or-empty]`, where
    // `comment = multiComment_ ["unannotated"]` iff `psInfo == Nothing`
    // (`annotated == false`).  `sep` lays method+comment inline when they
    // fit the ribbon, else drops the comment to its OWN line at the
    // step's base indent (`depth*2`).  We build the method as a Doc and
    // run it through the same HughesPJ engine so the break is
    // byte-identical to HS.
    let base = depth * 2;
    let annotated = node.annotated;
    let cases: Vec<(&String, &crate::constraint::solver::search::ProofNode)> =
        node.children.iter().collect();

    match (&node.method, cases.as_slice()) {
        (ProofMethod::Finished(MR::Solved), []) => {
            let doc = pp_step_doc(&node.method, "", msig);
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
        }
        (_, []) => {
            // No children: `by <step>` form.  HS `ppCases ps [] =
            // prettyCase ps (kwBy <> text " ") <> prettyStep ps` (non-diff
            // `prettyProofWith`, Theory/Proof.hs:1065-1066) — `<>` is beside, so the
            // `prettyStep` Doc is laid
            // out BESIDE `by `.  For a `SolveGoal` step the goal can wrap, and
            // HughesPJ counts the `by ` (3 cols) toward the ribbon when
            // deciding the `fsep`/`sep` break — so we must render `by ` as
            // line CONTENT, not as part of the indent (cf. the live string path;
            // the NAXOS/KAS2 `Match( a,` / `<…>` divergence).  The `by `
            // prefix is laid out by `step_line_with_unann` BESIDE the WHOLE
            // `sep [method, comment]` (HS `prettyCase ps (kwBy<>" ") <>
            // prettyStep ps`), so a dropped `/* unannotated */` aligns at
            // `base + len("by ")` (= +3), not `base`.  `beside` still shifts
            // the method's own wrapped continuation columns by the prefix
            // width and counts it toward the ribbon, so the method lines
            // stay byte-identical to HS.
            let doc = pp_step_doc(&node.method, "", msig);
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, "by "));
        }
        (_, [(label, child)]) if label.is_empty() => {
            let doc = pp_step_doc(&node.method, "", msig);
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
            out.push('\n');
            // HS `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf`
            // (non-diff `prettyProofWith`, Theory/Proof.hs:1054-1075, see line 1067).
            // `$-$` is "above" — the child is rendered
            // at the SAME indent column as the parent step.  In our output
            // model the caller writes the indent before calling pp_proof, so
            // we reproduce that here: write the same `depth`-level indent
            // before recursing into the child.
            out.push_str(&"  ".repeat(depth));
            pp_proof(child, out, depth, msig);
        }
        (_, multi) => {
            let doc = pp_step_doc(&node.method, "", msig);
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
            for (i, (name, child)) in multi.iter().enumerate() {
                if i > 0 {
                    // HS Theory/Proof.hs:1054-1075, see line 1070 (non-diff
                    // `prettyProofWith`): `intersperse (prettyCase ps kwNext)`
                    // — `next` is a sibling of `solve`/`qed`, so it sits at
                    // the parent's indent (`depth*2`), not column 0.
                    out.push('\n');
                    out.push_str(&"  ".repeat(depth));
                    out.push_str("next");
                }
                out.push('\n');
                let pad = "  ".repeat(depth + 1);
                out.push_str(&pad);
                out.push_str("case ");
                out.push_str(name);
                out.push('\n');
                out.push_str(&pad);
                pp_proof(child, out, depth + 1, msig);
            }
            out.push('\n');
            out.push_str(&"  ".repeat(depth));
            out.push_str("qed");
        }
    }
}

/// Render a `ProofMethod` to a flat string exactly as HS `prettyProofMethod`
/// (ProofMethod.hs:1173-1186) — the SAME renderer the `--prove` proof tree
/// uses, so `solve( <goal> )` carries the faithful fact spacing (`!KU( ~ltk )`),
/// LVar dots (`#vk.2`), and contradiction reasons.  Used by the interactive
/// web UI's applicable-methods list + proof snippet (`tamarin-server`), which
/// must match `--prove`'s method text.  Rendered at the process display width
/// (100 for the web); the semantic web gate normalises any wrapping away.
/// `sig` supplies the user-declared `[AC]` symbol names a `RawSolve`
/// method's stored goal text is re-parsed with.
pub fn pretty_proof_method_inline(
    m: &crate::constraint::solver::proof_method::ProofMethod,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> String {
    pp_step_doc(m, "", sig).render()
}

/// HS `prettyProofMethod m` as a Doc (ProofMethod.hs:1170-1186), for
/// callers that lay the method out INSIDE a larger Doc context — the web
/// "Applicable Proof Methods" list (`Web/Theory.hs:513-611, see line 546` `numbered' $
/// zipWith prettyPM [1..] pms`), where the `N. ` prefix beside-shift and
/// the trailing `// expl` line comment both participate in the HughesPJ
/// fill decisions.  `sig` supplies the user-declared `[AC]` symbol names a
/// `RawSolve` method's stored goal text is re-parsed with.
pub fn pretty_proof_method_doc(
    m: &crate::constraint::solver::proof_method::ProofMethod,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> crate::pretty_hpj::Doc {
    pp_step_doc(m, "", sig)
}

/// Build the proof-step method as a `pretty_hpj::Doc` so it can be
/// combined with the `/* unannotated */` comment via `sep`, per HS
/// `prettyIncrementalProof.ppStep`, ProofSkeleton.hs:80-84.
///
/// `prefix` is the leaf-step keyword (`"by "` for childless steps, `""`
/// otherwise); it is laid out BESIDE the method as line content (NOT
/// folded into the indent) so HughesPJ counts its columns toward the
/// ribbon, identical to `step_line_with_unann`/`pp_proof`'s string path.
fn pp_step_doc(
    m: &crate::constraint::solver::proof_method::ProofMethod,
    prefix: &str,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> crate::pretty_hpj::Doc {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::proof_method::{ProofMethod as PM, Result as MR};
    use crate::pretty_hpj::Doc;
    // `solve( <goal> )` builds its own goal Doc; everything else is a
    // flat string with no internal wrapping, so `Doc::text` of the
    // string form is faithful.
    let body = match m {
        PM::SolveGoal(g) => {
            let inner = match g {
                Goal::Disj(d) if !d.0.is_empty() => pf::disj_goal_to_doc(&d.0),
                _ => solve_goal_to_doc(g),
            };
            // HS `keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"`
            // (ProofMethod.hs:1181) — `solve(` and `)` are `hl_keyword` spans.
            crate::pretty_hpj::keyword_("solve(")
                .beside_sp(inner)
                .beside_sp(crate::pretty_hpj::keyword_(")"))
        }
        // A `RawSolve` is the display-only method kept for an unannotated
        // (replayed) subtree (replay.rs `parsed_to_unannotated`).  HS's
        // `noSystemPrf` (Theory/Proof.hs:447-467, see line 467 `mapProofInfo (\i -> (Just i,
        // Nothing))`) keeps the STRUCTURED `ProofMethod` (`SolveGoal goal`)
        // unchanged and re-renders it via `prettyProofMethod`
        // (ProofMethod.hs:1174-1187) → `prettyGoal` (Constraints.hs:273-287),
        // which RE-WRAPS the goal at the current `lineLength`/`ribbon`.  So
        // the stored `.spthy` layout (e.g. an `∃ #j.\n  (body)` break, or a
        // fact arg-list broken before `)`) must NOT be echoed verbatim: we
        // re-parse the goal text into a structured Doc and lay it out through
        // the same engine the live `SolveGoal` path uses, so HS reflows it inline.
        PM::RawSolve(raw) => raw_solve_to_doc(raw, msig),
        // HS `prettyProofMethod` (ProofMethod.hs:1183-1186):
        //   Finished (Contradictory reason) ->
        //     sep [ keyword_ "contradiction"
        //         , maybe emptyDoc (closedComment . prettyContradiction) reason ]
        // `closedComment d = comment $ fsep [text "/*", d, text "*/"]`
        // (Theory/Text/Pretty.hs:108-109).  Build this as a real Doc so HughesPJ's
        // `sep`/`fsep` break the comment (and its `/*`…`*/` delimiters)
        // onto their own lines at deep proof-tree indentation, identical
        // to HS.
        PM::Finished(MR::Contradictory(reason)) => {
            // HS `sep [keyword_ "contradiction", maybe emptyDoc (closedComment
            // . prettyContradiction) reason]` (ProofMethod.hs:1184-1186).
            let contra = crate::pretty_hpj::keyword_("contradiction");
            match reason {
                None => contra,
                Some(c) => {
                    // `closedComment d = comment (fsep [text "/*", d, text "*/"])`.
                    let inner = crate::pretty_hpj::comment(crate::pretty_hpj::fsep(vec![
                        Doc::text("/*"),
                        Doc::text(pp_contradiction(c)),
                        Doc::text("*/"),
                    ]));
                    crate::pretty_hpj::sep(vec![contra, inner])
                }
            }
        }
        // HS `prettyProofMethod` leaf keywords/comments (ProofMethod.hs:1175-1182).
        // Built as all-`beside` chains (no `fsep`) so plain-mode layout
        // matches HS exactly (the highlight combinators are the identity
        // there); HtmlDoc mode adds `hl_*` spans.
        PM::Simplify => crate::pretty_hpj::keyword_("simplify"),
        PM::Induction => crate::pretty_hpj::keyword_("induction"),
        PM::Finished(MR::Solved) => crate::pretty_hpj::keyword_("SOLVED")
            .beside_sp(crate::pretty_hpj::line_comment_("trace found")),
        PM::Finished(MR::Unfinishable) => crate::pretty_hpj::keyword_("UNFINISHABLE").beside_sp(
            crate::pretty_hpj::line_comment_("reducible operator in subterm"),
        ),
        PM::Invalidated => crate::pretty_hpj::line_comment_(
            "proof may have been invalidated by editing a reuse lemma above. You should ",
        ),
        // HS `Sorry reason -> fsep [keyword_ "sorry", maybe emptyDoc
        // closedComment_ reason]` (ProofMethod.hs:1179-1180).  `keyword_` is
        // identity in plain mode, so `sorry` / `sorry /* reason */`
        // matches HS exactly (verified against the `--prove` baseline); HtmlDoc
        // mode adds the `hl_keyword`/`hl_comment`
        // spans the overview `#proof` index needs.  `fsep [x, emptyDoc] = x`.
        PM::Sorry(reason) => match reason {
            None => crate::pretty_hpj::keyword_("sorry"),
            Some(r) => crate::pretty_hpj::fsep(vec![
                crate::pretty_hpj::keyword_("sorry"),
                crate::pretty_hpj::closed_comment_(r),
            ]),
        },
    };
    if prefix.is_empty() {
        body
    } else {
        Doc::text(prefix).beside(body)
    }
}

/// Render a `Goal` for the oracle/tactic ranking path.  This is HS's
/// `render $ prettyGoal g` from `ProofMethod.hs:604-622,700-702, see line 606,701`
/// (oracle stdin)
/// and `Tactics.hs` `pg = concat . lines . render $ prettyGoal agoal`
/// (tactic regex string).  All consumers (goals.rs oracle stdin /
/// `apply_ranking_fn` / `tactic_pg`) immediately apply `concat . lines`
/// to drop the newlines, so the byte-for-byte requirement is on each
/// line's internal text (leading indent spaces survive the `concat`).
///
/// Width: the oracle/tactic path uses plain `render = P.render`
/// (`Theory.Text.Pretty` re-exports `Text.PrettyPrint.Class.render`,
/// which is `P.render` from HughesPJ — Text/PrettyPrint/Class.hs:77-78).  `P.render`
/// uses HughesPJ's DEFAULT `style`: `lineLength = 100`,
/// `ribbonsPerLine = 1.5` → `ribbon = round(100/1.5) = 67`.  This is
/// DISTINCT from the `--prove` display path, which uses
/// `renderStyle (defaultStyle { lineLength = lineWidth })`
/// (Console.hs:242-243,398-399),
/// i.e. width 110 / ribbon 73 (`pretty_hpj::LINE_LENGTH`/`RIBBON`).
/// We build the goal via the same `solve_goal_to_doc` builder the
/// display path uses, then render it at the oracle width.
pub(crate) fn render_goal_for_oracle(g: &crate::constraint::constraints::Goal) -> String {
    // HS oracle stdin line = `show i ++": "++ (concat . lines . render $
    // prettyGoal g)` (ProofMethod.hs:598-623, see line 607).  HS `render` is HughesPJ's plain
    // `render` (= `fullRender`/`display` from line column 0), which APPLIES a
    // top-level `nest` to the FIRST line — so e.g. `prettyGoal (DisjG ..)` =
    // `fsep (map (nest 1 . parens . prettyGuarded) gfs)` renders with a LEADING
    // SPACE (`" (#a < #b)  ∥ .."`).  Use `render_with` (HughesPJ `lay`, indent
    // 0) here, NOT `render_at` (`lay2`, continuation mode) — `lay2` discards a
    // leading `Nest`, dropping that space and feeding the oracle a DIFFERENT
    // goal string than HS, which can change the oracle's ranking decisions.
    // (The `--prove` display path renders the disjunction AFTER a `solve( `
    // prefix, so the nest is never at the doc start there and both lay/lay2
    // agree — this divergence is oracle-stdin-specific.)
    //
    // ALWAYS plain: HS builds this string with the plain `render $
    // prettyGoal` regardless of the caller's rendering context
    // (ProofMethod.hs:598-623, see line 607).  The web proof-pane ranks while its
    // `HtmlDocGuard::enable()` is active — without forcing plain mode the
    // oracle receives `<span class=…>`/`&lt;`-laden goal strings its
    // regexes cannot match (dmn `*_min` panes ranked in bare goal-nr
    // order while HS's oracle reordered).
    let _plain = crate::pretty_hpj::HtmlDocGuard::disable();
    solve_goal_to_doc(g).render_with(ORACLE_LINE_LENGTH, ORACLE_RIBBON)
}

/// Build the `solve( <goal> )` Doc for an unannotated (replayed) step from
/// its raw goal text, re-rendering through the HS-faithful Doc engine.
///
/// HS `noSystemPrf` (Theory/Proof.hs:447-467, see line 467) keeps the parsed `SolveGoal goal`
/// structured, so `prettyProofMethod`/`prettyGoal` re-wraps it fresh.  We
/// recover the structure from the raw `solve(...)` inner text and route it
/// through the SAME builders the live-goal path uses
/// (`pf::fact_doc`/`pf::term_doc`/`pf::disj_goal_to_doc`), so the wrapping
/// is byte-identical to HS regardless of how the stored `.spthy` was laid
/// out.  Goal shapes we cannot structurally recover (chain / `Raw`) fall
/// back to the verbatim text — those goals are short and never wrap, so HS
/// renders them on one line too.
///
/// `msig` reaches the re-parses through [`raw_goal_to_doc`].
fn raw_solve_to_doc(raw: &str, msig: &tamarin_term::maude_sig::MaudeSig) -> crate::pretty_hpj::Doc {
    // Mirror HS `SolveGoal goal -> keyword_ "solve(" <-> prettyGoal goal <->
    // keyword_ ")"` (ProofMethod.hs:1181): the `solve(` / `)` delimiters are
    // `hl_keyword` spans (identity in plain mode, so batch bytes are
    // unchanged).  The unannotated-replay overview index (`hl_superfluous`
    // steps) needs these spans to match HS.
    let goal_doc = raw_goal_to_doc(raw, msig);
    crate::pretty_hpj::keyword_("solve(")
        .beside_sp(goal_doc)
        .beside_sp(crate::pretty_hpj::keyword_(")"))
}

/// Re-render the goal text inside a `solve( ... )` (the part between the
/// parens) as a Doc.  Mirrors HS `prettyGoal` (Constraints.hs:273-287) by
/// reconstructing each goal kind from `parse_goal_spec`
/// (`proof_tree.rs`) and laying it out with the live-goal builders.
///
/// `msig` is the signature the stored text was rendered against, which each
/// re-parse needs for the user `[AC]` symbols' infix spelling and the
/// arity-0 constants — HS's parser reads both from the signature in parser
/// state (Theory/Text/Parser/Term.hs:158-174).
fn raw_goal_to_doc(raw: &str, msig: &tamarin_term::maude_sig::MaudeSig) -> crate::pretty_hpj::Doc {
    use crate::guarded::formula_to_guarded_parsed;
    use crate::pretty_hpj::Doc;
    use tamarin_parser::ast::GoalSpec;
    use tamarin_parser::parser::{parse_formula_str, parse_term_str};
    use tamarin_parser::proof_tree::parse_goal_spec;

    let trimmed = raw.trim();
    match parse_goal_spec(trimmed) {
        // `prettyGoal (ActionG i fa) = prettyFact fa <-> "@" <-> show i`.
        // `show i` (HS `Show LVar`) keeps the timepoint idx: `#vk.6`, not
        // `#vk`.  Reconstruct the node LVar and render via `render_lvar`
        // (the same renderer the live-goal path uses, render_node_id) so
        // the head is byte-identical to HS's re-render.
        GoalSpec::Action {
            fact,
            time_var,
            time_idx,
        } => reparse_fact_doc(&fact, msig)
            .beside_sp(crate::pretty_hpj::operator_("@"))
            .beside_sp(Doc::text(render_node_id_str(&time_var, time_idx))),
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> "▶"<>subscript v <-> prettyNodeId i`.
        GoalSpec::Premise {
            fact,
            prem_idx,
            time_var,
            time_idx,
        } => reparse_fact_doc(&fact, msig)
            .beside_sp(Doc::text(format!("\u{25B6}{}", goal_subscript(prem_idx))))
            .beside_sp(Doc::text(render_node_id_str(&time_var, time_idx))),
        // `prettyGoal (DisjG (Disj gfs)) =
        //    fsep $ punctuate "  ∥" (map (nest 1 . parens . prettyGuarded) gfs)`.
        // Re-parse each disjunct's text into a Guarded and route through the
        // same `disj_goal_to_doc` the live path uses.  If ANY disjunct fails
        // to re-parse, fall back to verbatim (the rare unparseable case then
        // renders as stored).
        GoalSpec::Disj { .. } => match parse_disjuncts_to_guarded(trimmed, msig) {
            Some(gfs) => pf::disj_goal_to_doc(&gfs),
            None => Doc::text(trimmed),
        },
        // `prettyGoal (SubtermG (l,r)) = prettyLNTerm l <-> "⊏" <-> prettyLNTerm r`.
        GoalSpec::Subterm { small_raw, big_raw } => {
            match (
                parse_term_str(small_raw.trim(), msig),
                parse_term_str(big_raw.trim(), msig),
            ) {
                (Ok(l), Ok(r)) => pf::term_doc(&l)
                    .beside_sp(crate::pretty_hpj::operator_("\u{228F}"))
                    .beside_sp(pf::term_doc(&r)),
                _ => Doc::text(trimmed),
            }
        }
        // `splitEqs(N)` never wraps; keep verbatim.
        GoalSpec::Split { .. } => Doc::text(trimmed),
        // `prettyGoal (ChainG c p) = prettyNodeConc c <-> operator_ "~~>" <->
        //  prettyNodePrem p` (Constraints.hs).  The endpoints render as plain
        // node text; only the `~~>` arrow is an `hl_operator` span.  The stored
        // goal text is exactly `<conc> ~~> <prem>`, so split on the arrow.
        GoalSpec::Chain { .. } => match trimmed.split_once("~~>") {
            Some((l, r)) => Doc::text(l.trim_end())
                .beside_sp(crate::pretty_hpj::operator_("~~>"))
                .beside_sp(Doc::text(r.trim_start())),
            None => Doc::text(trimmed),
        },
        // Unrecognised goal shapes: a lone guarded formula goal (e.g. a
        // single quantified alt) parses here.  Try formula→guarded so it
        // re-wraps like HS's `prettyGuarded`; else keep verbatim.
        GoalSpec::Raw(_) => {
            match parse_formula_str(trimmed, msig)
                .ok()
                .and_then(|f| formula_to_guarded_parsed(&f, msig).ok())
            {
                Some(g) => pf::disj_goal_to_doc(std::slice::from_ref(&g)),
                None => Doc::text(trimmed),
            }
        }
    }
}

/// Render an Action/Premise goal's `Fact` to a Doc, RE-PARSING each
/// argument's term text into a structured term first.
///
/// `parse_goal_spec`'s Action/Premise parser (`build_fact` in
/// `proof_tree.rs`) is a goal-MATCHING shim — it does NOT parse the
/// argument terms, instead stuffing each top-level-comma-split arg's RAW
/// TEXT (incl. any stored newlines / wrapping) into a `Term::Var` name.
/// Rendering that via `pf::fact_doc` directly would echo the stored layout
/// verbatim (the dnp3 `senc(<…>)` tuple wrapped exactly as the input file
/// had it).  Here we re-parse each arg's text with `parse_term_str` so the
/// fact's terms get their real structure and re-wrap through the Doc engine
/// like HS's `prettyLNFact`.  If any arg fails to re-parse we keep that
/// arg's raw text (it still renders, just not re-flowed) — a strictly
/// no-worse fallback.
///
/// `msig` is the signature the stored text was rendered against, so the
/// re-parse reads a user `[AC]` symbol's infix spelling (`x add y`) — HS's
/// `acterm` takes the same set from the signature in parser state
/// (Theory/Text/Parser/Term.hs:166-172).
fn reparse_fact_doc(
    fact: &tamarin_parser::ast::Fact,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> crate::pretty_hpj::Doc {
    use tamarin_parser::ast::{Fact, Term};
    use tamarin_parser::parser::parse_term_str;
    let args: Vec<Term> = fact
        .args
        .iter()
        .map(|a| match a {
            // `build_fact` stored the raw arg text as a `Var` name; re-parse it.
            Term::Var(v) => parse_term_str(v.name.trim(), msig).unwrap_or_else(|_| a.clone()),
            other => other.clone(),
        })
        .collect();
    let reparsed = Fact {
        persistent: fact.persistent,
        name: fact.name.clone(),
        args,
        annotations: fact.annotations.clone(),
    };
    pf::fact_doc(&reparsed)
}

/// Split the `solve(...)` disjunction text at top-level `∥`, re-parsing
/// each disjunct as a guarded formula (HS `disjSplitGoal` parses each
/// disjunct as a full `Guarded`, Theory/Text/Parser/Proof.hs:39-72, see line 61).  Returns
/// `None` if any disjunct fails to parse (caller falls back to verbatim).
fn parse_disjuncts_to_guarded(
    text: &str,
    msig: &tamarin_term::maude_sig::MaudeSig,
) -> Option<Vec<crate::guarded::Guarded>> {
    use crate::guarded::formula_to_guarded_parsed;
    use tamarin_parser::parser::parse_formula_str;
    let parts = split_top_level_disj_par(text);
    let mut out = Vec::with_capacity(parts.len());
    for p in &parts {
        let inner = strip_one_outer_paren(p.trim());
        let f = parse_formula_str(inner, msig).ok()?;
        let g = formula_to_guarded_parsed(&f, msig).ok()?;
        out.push(g);
    }
    Some(out)
}

/// Split `s` at top-level `∥` (U+2225), ignoring separators inside
/// `()/[]/{}` brackets.  Mirrors the parser's `split_top_level_disj`
/// (`proof_tree.rs`) so the disjunct boundaries match `parse_goal_spec`'s.
fn split_top_level_disj_par(s: &str) -> Vec<String> {
    const SEP: char = '\u{2225}';
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => {
                depth += 1;
                cur.push(c);
            }
            ')' | ']' | '}' => {
                depth -= 1;
                cur.push(c);
            }
            _ if c == SEP && depth == 0 => out.push(std::mem::take(&mut cur)),
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Strip ONE balanced outer `(...)` layer if the whole string is wrapped
/// in it; otherwise return the string unchanged.  Each disjunct in a
/// `solve( (g1) ∥ (g2) )` carries its own `opParens` wrap (HS `map opParens`
/// in `prettyGuarded`'s GDisj, Guarded.hs:824-866, see line 836), which `parse_formula_str`
/// would otherwise re-wrap — strip it so the re-parsed guarded matches the
/// live-goal `Guarded` (which has no outer-paren node).
fn strip_one_outer_paren(s: &str) -> &str {
    let s = s.trim();
    let bytes = s.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'(' || bytes[bytes.len() - 1] != b')' {
        return s;
    }
    let mut depth: i32 = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                // A depth-0 close before the final char means the leading
                // `(` does NOT match the trailing `)` — don't strip.
                if depth == 0 && i != s.len() - 1 {
                    return s;
                }
            }
            _ => {}
        }
    }
    &s[1..s.len() - 1]
}

/// Build a `pretty_hpj::Doc` for a non-DisjG `Goal`, mirroring HS
/// `prettyGoal` (Constraints.hs:273-287).  `<->` = `<+>` (beside-with-
/// space).  Facts go through `prettyLNFact`'s `nestShort'` wrapping (via
/// `pf::fact_doc`); terms through `prettyLNTerm` (via `pf::term_doc`);
/// node-ids / node-conc / node-prem are atomic strings (HS `prettyNodeId`
/// is `text . show`).  The non-empty DisjG case is rendered by the
/// `disj_goal_to_doc` arm below.
pub(crate) fn solve_goal_to_doc(
    g: &crate::constraint::constraints::Goal,
) -> crate::pretty_hpj::Doc {
    use crate::constraint::constraints::Goal;
    use crate::pretty_hpj::Doc;
    use crate::rule::PremIdx;
    match g {
        // `prettyGoal (ActionG i fa) = prettyNAtom (Action (varTerm i) fa)`
        // = `prettyFact fa <-> opAction <-> text (show i)` (Atom.hs:216-217),
        // `opAction = "@"` (Theory/Text/Pretty.hs:170).
        Goal::Action(i, fa) => {
            let nid = render_node_id(i);
            pf::fact_doc(&lnfact_to_parser(fa))
                .beside_sp(crate::pretty_hpj::operator_("@"))
                .beside_sp(Doc::text(nid))
        }
        // `prettyGoal (ChainG c p) =
        //    prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p`.
        Goal::Chain(c, p) => Doc::text(render_node_conc(c))
            .beside_sp(crate::pretty_hpj::operator_("~~>"))
            .beside_sp(Doc::text(render_node_prem(p))),
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i`.
        Goal::Premise((i, PremIdx(v)), fa) => {
            let sub = goal_subscript(*v);
            let nid = render_node_id(i);
            pf::fact_doc(&lnfact_to_parser(fa))
                .beside_sp(Doc::text(format!("\u{25B6}{}", sub)))
                .beside_sp(Doc::text(nid))
        }
        // `prettyGoal (SplitG x) = text "splitEqs" <> parens (text (show ...))`
        // `<>` = no space → `splitEqs(N)`.
        Goal::Split(id) => Doc::text(format!("splitEqs({})", id.0)),
        // `prettyGoal (DisjG (Disj [])) = text "Disj" <-> operator_ "(⊥)"`.
        Goal::Disj(d) if d.0.is_empty() => {
            Doc::text("Disj").beside_sp(crate::pretty_hpj::operator_("(\u{22A5})"))
        }
        // Non-empty DisjG renders via the Doc form (`disj_goal_to_doc`).
        Goal::Disj(d) => pf::disj_goal_to_doc(&d.0),
        // `prettyGoal (SubtermG (l,r)) =
        //    prettyLNTerm l <-> operator_ "⊏" <-> prettyLNTerm r`.
        Goal::Subterm((l, r)) => pf::term_doc(&lnterm_to_parser(l))
            .beside_sp(crate::pretty_hpj::operator_("\u{228F}"))
            .beside_sp(pf::term_doc(&lnterm_to_parser(r))),
    }
}

/// Render a `NodeId` (`LVar` of Node sort).  HS `prettyNodeId`
/// (LTerm.hs:926-927) is `text . show`, where `Show LVar`
/// (LTerm.hs:550-557) yields `<sortPrefix><name>` (or `<...>.<idx>`).
fn render_node_id(nid: &crate::constraint::constraints::NodeId) -> String {
    render_lvar(nid)
}

/// Render a `NodeConc`.  Mirrors HS `prettyNodeConc`
/// (Constraints.hs:256-257): `parens (prettyNodeId v <> comma <-> int i)`.
/// `<>` joins with no space; `<->` adds a space — `(#i, 0)`.
fn render_node_conc(c: &crate::constraint::constraints::NodeConc) -> String {
    format!("({}, {})", render_node_id(&c.0), (c.1).0)
}

/// Render a `NodePrem`.  Mirrors HS `prettyNodePrem`
/// (Constraints.hs:260-261): same layout as `prettyNodeConc`.
fn render_node_prem(p: &crate::constraint::constraints::NodePrem) -> String {
    format!("({}, {})", render_node_id(&p.0), (p.1).0)
}

/// Unicode-subscript digits for a non-negative integer.  Mirrors HS
/// `subscript` used by `prettyGoal (PremiseG …)` in Constraints.hs:273-288.
fn goal_subscript(n: usize) -> String {
    tamarin_utils::unicode::subscript(&n.to_string())
}

fn pp_contradiction(c: &crate::constraint::solver::contradictions::Contradiction) -> String {
    use crate::constraint::solver::contradictions::Contradiction as C;
    // HS `prettyContradiction` (Contradictions.hs:487-506).
    match c {
        C::Cyclic => "cyclic".to_string(),
        // HS: `SubtermCyclic -> text "contradictory subterm store"`
        C::SubtermCyclic => "contradictory subterm store".to_string(),
        C::IncompatibleEqs => "incompatible equalities".to_string(),
        C::NonNormalTerms => "non-normal terms".to_string(),
        // HS: `ForbiddenExp -> text "non-normal exponentiation rule instance"`
        C::ForbiddenExp => "non-normal exponentiation rule instance".to_string(),
        // HS: `ForbiddenBP -> text "non-normal bilinear pairing rule instance"`
        C::ForbiddenBP => "non-normal bilinear pairing rule instance".to_string(),
        // HS: `ForbiddenKD -> text "forbidden KD-fact"`
        C::ForbiddenKD => "forbidden KD-fact".to_string(),
        C::ForbiddenChain => "forbidden chain".to_string(),
        C::ForbiddenACConstrChain => "forbidden AC constructor chain".to_string(),
        C::ImpossibleChain => "impossible chain".to_string(),
        // HS: `NonInjectiveFactInstance cex -> text $ "non-injective facts " ++ show cex`
        // where `cex :: (NodeId, NodeId, NodeId)`.  HS `Show` for a
        // tuple yields `(a,b,c)` (no spaces after commas), with each
        // component rendered by `Show LVar` (LTerm.hs:550-557) — which
        // is identical to our `render_lvar`.
        C::NonInjectiveFactInstance(a, b, c) => format!(
            "non-injective facts ({},{},{})",
            render_lvar(a),
            render_lvar(b),
            render_lvar(c)
        ),
        C::FormulasFalse => "from formulas".to_string(),
        // HS: `SuperfluousLearn m v ->
        //        doubleQuotes (prettyLNTerm m) <->
        //        text "derived before and after" <->
        //        doubleQuotes (prettyNodeId v)`
        // → `"<m>" derived before and after "<v>"`.
        C::SuperfluousLearn(m, v) => format!(
            "\"{}\" derived before and after \"{}\"",
            tamarin_term::pretty::pretty_lnterm(m),
            render_node_id(v)
        ),
        // HS: `NodeAfterLast (i,j) ->
        //        text $ "node " ++ show j ++ " after last node " ++ show i`
        // Note HS reverses the order: `j` first in the message, then `i`.
        C::NodeAfterLast(i, j) => {
            format!("node {} after last node {}", render_lvar(j), render_lvar(i))
        }
    }
}

// =============================================================================
// Generated-from
// =============================================================================

fn render_generated_from(build: &BuildInfo) -> String {
    format!(
        "/*\nGenerated from:\nTamarin version {}\nMaude version {}\nGit revision: {}, branch: {}\nCompiled at: {}\n*/",
        build.tamarin_version,
        build.maude_version,
        build.git_revision,
        build.git_branch,
        build.compiled_at,
    )
}

#[cfg(test)]
mod oracle_goal_tests {
    use super::*;
    use crate::constraint::constraints::Goal;
    use crate::fact::{Fact, FactTag, LNFact, Multiplicity};
    use crate::rule::PremIdx;
    use tamarin_term::lterm::{LNTerm, LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    fn fresh(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Fresh, 0)))
    }

    /// The oracle/tactic ranking string is HS's `concat . lines . render`,
    /// where `render = P.render` uses HughesPJ's default `style`
    /// (lineLength = 100, ribbon = 67) — NOT the `--prove` DISPLAY width
    /// (110 / 73, used by `renderStyle (defaultStyle { lineLength = lineWidth })`
    /// in Console.hs:242-243,398-399).
    ///
    /// Authentic ground truth (captured from the v1.13.0 HS prover with an
    /// oracle that echoes stdin, on a crafted theory whose premise goal is
    /// 69 columns wide):
    ///
    /// ```text
    /// 0: !KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb) ▶₀ #l
    /// ```
    ///
    /// Note the absence of a space before the closing `)`: at ribbon 67 the
    /// fact's `nestShort'` (Theory/Model/Fact.hs:567-574, see line 572) wraps,
    /// pushing `)` onto its own
    /// line at column 0, and `concat . lines` then joins it directly to the
    /// preceding `~msgbbbbbbbbbbbbbbbbbbbb`.  At the DISPLAY ribbon 73 the same
    /// goal stays inline (`... ~msgbbbbbbbbbbbbbbbbbbbb )`, with the space).
    /// That single byte distinguishes the two widths, so it pins the oracle
    /// path to 100/67.
    #[test]
    fn premise_goal_wraps_at_oracle_ribbon_67() {
        // !KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb ) ▶₀ #l
        let fa: LNFact = Fact::new(
            FactTag::Proto(Multiplicity::Persistent, "KeyStore0", 2),
            vec![
                fresh("keyaaaaaaaaaaaaaaaaaaaa"),
                fresh("msgbbbbbbbbbbbbbbbbbbbb"),
            ],
        );
        let node = LVar::new("l", LSort::Node, 0);
        let goal = Goal::Premise((node, PremIdx(0)), fa);

        // HS: `concat . lines . render $ prettyGoal g`.
        let rendered = render_goal_for_oracle(&goal);
        let collapsed: String = rendered.lines().collect::<Vec<_>>().concat();

        assert_eq!(
            collapsed,
            "!KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb) \u{25B6}\u{2080} #l",
            "oracle goal string must match HS `render` at default ribbon 67 \
             (wrapped fact: no space before `)`)",
        );

        // The SAME goal at the DISPLAY width (110 / 73) stays inline, keeping
        // the space before `)`.  This guards against silently swapping the
        // oracle width back to the display width.
        let display: String = solve_goal_to_doc(&goal)
            .render_at(crate::pretty_hpj::LINE_LENGTH, crate::pretty_hpj::RIBBON, 0)
            .lines()
            .collect::<Vec<_>>()
            .concat();
        assert_eq!(
            display,
            "!KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb ) \u{25B6}\u{2080} #l",
            "display width must keep the fact inline (space before `)`); the two \
             expectations differ by exactly that byte, which is what makes this \
             pair discriminating",
        );
    }

    /// Regression: a disjunction goal sent to the oracle MUST carry the
    /// leading space HS produces.  HS `prettyGoal (DisjG (Disj gfs))` =
    /// `fsep (map (nest 1 . parens . prettyGuarded) gfs)` (Constraints.hs:
    /// 276-277), and HS `render` (HughesPJ `lay`, from column 0) APPLIES the
    /// top-level `nest 1` to the FIRST line — so the oracle stdin line is
    /// `" (#a < #b)  ∥ (#b < #a)"` (leading space).  `render_goal_for_oracle`
    /// must use `render_with`/`lay`, NOT `render_at`/`lay2` (which drops a
    /// leading `Nest`); the latter fed the oracle a string differing from HS
    /// by one space, perturbing oracle ranking decisions on oracle-driven
    /// proofs (e.g. csf19-wrapping gcm).  Ground truth captured from the
    /// v1.13.0 HS prover with an echoing oracle.
    #[test]
    fn disj_goal_for_oracle_has_leading_space() {
        use crate::constraint::constraints::{Disj, Goal};
        use crate::guarded::Guarded;
        use crate::guarded_types::{BVar, GAtom, GTerm};
        use tamarin_parser::ast::VarSpec;
        use tamarin_term::lterm::LSort;

        let tp = |n: &str| {
            GTerm::Var(BVar::Free(VarSpec {
                name: n.to_string(),
                idx: 0,
                sort: LSort::Node,
                typ: None,
            }))
        };
        // `#a < #b` ∥ `#b < #a`
        let d1 = Guarded::Atom(GAtom::Less(tp("a"), tp("b")));
        let d2 = Guarded::Atom(GAtom::Less(tp("b"), tp("a")));
        let goal = Goal::Disj(Disj::new(vec![d1, d2]));

        let rendered = render_goal_for_oracle(&goal);
        let collapsed: String = rendered.lines().collect::<Vec<_>>().concat();
        // HS `nest 1` leading space + `"  ∥"` separator (two spaces + ∥).
        assert_eq!(
            collapsed, " (#a < #b)  \u{2225} (#b < #a)",
            "oracle disjunction goal must keep HS's leading `nest 1` space; \
             losing it is the render_at/lay2 regression",
        );
    }
}

#[cfg(test)]
mod manual_rule_variants_tests {
    use super::*;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
    use crate::signature::SignaturePure;
    use crate::theory::{OpenProtoRule, TheoryItem};

    fn parsed_rule(name: &str) -> p::TheoryItem {
        p::TheoryItem::Rule(p::Rule {
            name: name.to_string(),
            modulo: None,
            attributes: vec![],
            let_block: vec![],
            premises: vec![],
            actions: vec![],
            conclusions: vec![],
            embedded_restrictions: vec![],
            variants: vec![],
            left_right: None,
        })
    }

    /// An elaborated rule named `name`, carrying `action_names` as actions.
    fn elab_rule(name: &str, action_names: &[&str]) -> TheoryItem {
        let acts = action_names
            .iter()
            .map(|a| proto_fact(Multiplicity::Linear, a, vec![]))
            .collect();
        let r: ProtoRuleE = Rule::new(ProtoRuleEInfo::standard(name), vec![], vec![], acts);
        TheoryItem::Rule(OpenProtoRule::new(r))
    }

    fn theories(names: &[&str], elab: Vec<TheoryItem>) -> (p::Theory, Theory) {
        let parsed = p::Theory {
            is_diff: false,
            name: "T".to_string(),
            configuration: None,
            items: names.iter().map(|n| parsed_rule(n)).collect(),
        };
        let mut elaborated: Theory = Theory::new("T", SignaturePure::empty(false));
        elaborated.items = elab;
        (parsed, elaborated)
    }

    /// The same OR computed with the renderer's positional
    /// `(name, occurrence-ordinal)` pairing instead of the name-keyed
    /// lookup.
    fn positional(parsed: &p::Theory, elaborated: &Theory, auto_sources: bool) -> bool {
        let paired = pair_elaborated_rules(&parsed.items, elaborated);
        parsed
            .items
            .iter()
            .zip(paired)
            .any(|(item, er)| match item {
                p::TheoryItem::Rule(r) => rule_open_ac_nonempty(r, er, auto_sources),
                _ => false,
            })
    }

    /// Partial evaluation refines one rule into several of the SAME name;
    /// auto-sources then annotates them by name, so every member of a
    /// same-name group carries the same `AUTO_*` action.  On that shape the
    /// name-keyed lookup and the positional pairing agree.
    #[test]
    fn auto_actions_are_uniform_across_same_named_rules() {
        let auto_out = "AUTO_OUT_TERM_1_0_0__Recv";
        let (parsed, elaborated) = theories(
            &["Send", "Send", "Recv"],
            vec![
                elab_rule("Send", &[auto_out]),
                elab_rule("Send", &[auto_out]),
                elab_rule("Recv", &["AUTO_IN_TERM_1_0_0__Recv"]),
            ],
        );
        assert!(contains_manual_rule_variants(&parsed, &elaborated, true));
        assert_eq!(
            contains_manual_rule_variants(&parsed, &elaborated, true),
            positional(&parsed, &elaborated, true),
        );
        // The gate is an OR over the rules.  The mixed theory above still
        // fires if the discriminant loses one of the two prefixes.  Each
        // prefix therefore gets a single-rule theory of its own.
        for auto in [auto_out, "AUTO_IN_TERM_1_0_0__Recv"] {
            let (parsed, elaborated) = theories(&["R"], vec![elab_rule("R", &[auto])]);
            assert!(
                contains_manual_rule_variants(&parsed, &elaborated, true),
                "{auto} alone must open the gate",
            );
            assert!(
                !contains_manual_rule_variants(&parsed, &elaborated, false),
                "{auto} must be invisible without --auto-sources",
            );
        }
    }

    /// A theory whose duplicated rules carry no `AUTO_*` action leaves the
    /// gate off — under both resolutions.
    #[test]
    fn no_auto_action_leaves_the_gate_off() {
        let (parsed, elaborated) = theories(
            &["Send", "Send", "Recv"],
            vec![
                elab_rule("Send", &["Plain"]),
                elab_rule("Send", &["Plain"]),
                elab_rule("Recv", &[]),
            ],
        );
        assert!(!contains_manual_rule_variants(&parsed, &elaborated, true));
        assert_eq!(
            contains_manual_rule_variants(&parsed, &elaborated, true),
            positional(&parsed, &elaborated, true),
        );
    }

    /// Without `--auto-sources` the elaborated rule is not consulted at all:
    /// the gate is the parsed items' `variants` blocks, which the refined
    /// rules partial evaluation emits never have.
    #[test]
    fn without_auto_sources_the_elaborated_rule_is_not_consulted() {
        let auto_out = "AUTO_OUT_TERM_1_0_0__Recv";
        let (parsed, elaborated) = theories(
            &["Send", "Send"],
            vec![
                elab_rule("Send", &[auto_out]),
                elab_rule("Send", &[auto_out]),
            ],
        );
        assert!(!contains_manual_rule_variants(&parsed, &elaborated, false));
        assert_eq!(
            contains_manual_rule_variants(&parsed, &elaborated, false),
            positional(&parsed, &elaborated, false),
        );
    }
}

#[cfg(test)]
mod stored_proof_reparse_tests {
    use super::*;

    /// A stored `solve( ... )` step is re-rendered by re-parsing its goal
    /// text, and that re-parse reads a user `[AC]` symbol's INFIX spelling
    /// only when the signature it is seeded with declares the symbol — HS's
    /// `acterm` takes the same set from the signature in parser state
    /// (Theory/Text/Parser/Term.hs:166-172).
    #[test]
    fn reparse_reads_user_ac_infix_from_the_signature() {
        let thy =
            tamarin_parser::parser::parse_theory("theory T begin\nfunctions: add/2 [AC]\nend", &[])
                .unwrap();
        let elaborated = crate::elaborate::elaborate(&thy).unwrap();
        let msig = &elaborated.signature.maude_sig;

        let raw = "!KU( (x add\n         y) ) @ #i";
        assert_eq!(
            raw_solve_to_doc(raw, msig).render(),
            "solve( !KU( (x add y) ) @ #i )",
        );
        // Without the declaration the infix spelling is not a term, so the
        // argument stays the stored text, wrapping and all.
        assert_eq!(
            raw_solve_to_doc(raw, &tamarin_term::maude_sig::pair_maude_sig()).render(),
            "solve( !KU( (x add\n         y) ) @ #i )",
        );
    }
}

#[cfg(test)]
mod lnatom_to_parser_tests {
    use super::*;
    use crate::atom::{Atom, ProtoAtom};
    use crate::fact::{Fact, FactTag, Multiplicity};
    use tamarin_term::intern::intern_str;
    use tamarin_term::lterm::{LNTerm, LSort, LVar};
    use tamarin_term::vterm::var_term;

    fn pvar(name: &str, sort: LSort) -> p::Term {
        p::Term::Var(p::VarSpec {
            name: name.to_string(),
            idx: 0,
            sort,
            typ: None,
        })
    }

    /// HS writes an action atom as `Action t (Fact t)` (Atom.hs:78) and the
    /// parser AST as `Action(Fact, Term)`, so the two operands swap places.
    #[test]
    fn lnatom_to_parser_keeps_the_action_timepoint_and_fact() {
        let x: LNTerm = var_term(LVar::new("x", LSort::Msg, 0));
        let i: LNTerm = var_term(LVar::new("i", LSort::Node, 0));
        let fa = Fact::new(
            FactTag::Proto(Multiplicity::Linear, intern_str("Ev"), 1),
            vec![x],
        );
        let a: Atom<LNTerm> = ProtoAtom::Action(i, fa);
        assert_eq!(
            lnatom_to_parser(&a),
            p::Atom::Action(
                p::Fact {
                    persistent: false,
                    name: "Ev".to_string(),
                    args: vec![pvar("x", LSort::Msg)],
                    annotations: Vec::new(),
                },
                pvar("i", LSort::Node),
            )
        );
    }

    /// The binary atoms keep their left and right operand where they are.
    #[test]
    fn lnatom_to_parser_keeps_the_binary_operand_order() {
        let i: LNTerm = var_term(LVar::new("i", LSort::Node, 0));
        let j: LNTerm = var_term(LVar::new("j", LSort::Node, 0));
        let a: Atom<LNTerm> = ProtoAtom::Less(i, j);
        assert_eq!(
            lnatom_to_parser(&a),
            p::Atom::Less(pvar("i", LSort::Node), pvar("j", LSort::Node))
        );
    }
}

#[cfg(test)]
mod predicate_echo_tests {
    use super::*;

    /// HS `prettyPredicate` (TheoryObject.hs:845-849) lays the predicate's
    /// fact and formula out with `render`, HughesPJ's default style, and
    /// embeds the two as one `text`.  That style is 100 columns with 1.5
    /// ribbons per line, which `fullRender` rounds to a ribbon of 67
    /// (HughesPJ.hs:940, :1010), while the theory echo around the predicate
    /// item is laid out by the console's `renderDoc` at 110/73.  So a
    /// predicate formula breaks where 67 columns of ribbon run out, not
    /// where 73 do: `Between`'s inner conjunction is 68 columns wide and
    /// breaks, and its second operand starts a line of its own.
    ///
    /// Expected string: the pinned oracle's bytes for this theory.
    #[test]
    fn predicate_formula_wraps_at_the_default_style() {
        const SRC: &str = "theory P4PredWidth\n\
begin\n\
rule R:\n  [ In( x ) ] --[ Ev( x ) ]-> [ ]\n\
predicate: Between(x, y, z) <=> \
(Ex #i #j #k. Ev(x) @ #i & Ev(y) @ #j & Ev(z) @ #k & #i < #j & #j < #k)\n\
end\n";
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let predicates = collect_predicates(&parsed);
        // The theory declares no arity-1 no-eq function.
        #[allow(clippy::disallowed_types)]
        let arity1 = std::collections::HashSet::new();
        assert_eq!(
            render_predicate(&predicates[0], &arity1),
            concat!(
                "predicate: Between( x, y, z )<=>\u{2203} #i #j #k.\n",
                " ((((Ev( x ) @ #i) \u{2227} (Ev( y ) @ #j)) \u{2227} (Ev( z ) @ #k)) \u{2227}\n",
                "  (#i < #j)) \u{2227}\n",
                " (#j < #k)",
            )
        );
    }
}

#[cfg(test)]
mod closed_restriction_tests {
    use super::*;

    /// The fixture theory of `scripts/divergence_fixtures/s3_macro_lemma_header.spthy`,
    /// cut to its restrictions: `MacroRestriction` calls a macro and a
    /// predicate, `PlainRestriction` neither.
    const SRC: &str = "theory S3MacroLemmaHeader\n\
begin\n\
predicates:\n  IsPairOf(m, a, b) <=> m = <a, b>\n\
macros:\n  tag(x) = <'t', x>, wrap(x, y) = tag(<x, y>)\n\
rule A:\n  [ In( <x, y> ) ] --[ A( wrap(x, y) ) ]-> [ Out( tag(x) ) ]\n\
restriction PlainRestriction:\n  \"All m #i. A( m ) @ #i ==> not( m = 'no' )\"\n\
restriction MacroRestriction:\n  \"All m x y #i. A( m ) @ #i & IsPairOf(m, x, y) ==> m = wrap(x, y)\"\n\
end\n";

    /// HS `prettyRestriction` quotes `fromMaybe expandedFormula ogFormula`
    /// above the block and `expandedFormula` inside it
    /// (TheoryObject.hs:893, :895-898), and `applyMacroInRestriction` fills
    /// `ogFormula` with the pre-macro formula
    /// (Theory/Model/Restriction.hs:164-166).  So the macro call `wrap(x, y)`
    /// stands on top and its expansion `<'t', x, y>` in the block, while the
    /// predicate atom `IsPairOf(m, x, y)` is inlined in both — parse-time
    /// expansion, which `liftedAddRestriction` runs over the stored formula
    /// and its original alike (Theory/Text/Parser.hs:129-139).
    ///
    /// Expected strings are the pinned oracle's bytes for the fixture
    /// (`scripts/divergence_fixtures/expected/s3_macro_lemma_header.theory.hs.txt`).
    #[test]
    fn closed_restriction_prints_the_original_on_top_and_the_expanded_in_the_block() {
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let elaborated = crate::elaborate::elaborate(&parsed).expect("theory elaborates");
        let rendered = web_restrictions(&parsed, &elaborated);
        assert_eq!(
            rendered,
            vec![
                "restriction PlainRestriction:\n  \
                 \"∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))\"\n  \
                 // safety formula\n\n  \
                 /*\n  expanded formula:\n  \
                 \"∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))\"\n  */",
                "restriction MacroRestriction:\n  \
                 \"∀ m x y #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ⇒ (m = wrap(x, y))\"\n  \
                 // safety formula\n\n  \
                 /*\n  expanded formula:\n  \
                 \"∀ m x y #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ⇒ (m = <'t', x, y>)\"\n  */",
            ]
        );
    }
}

#[cfg(test)]
mod closed_lemma_tests {
    use super::*;

    /// The fixture theory of `scripts/divergence_fixtures/s3_macro_lemma_header.spthy`,
    /// cut to its lemmas: `MacroLemma` calls a macro and a predicate,
    /// `PlainLemma` neither.
    const SRC: &str = "theory S3MacroLemmaHeader\n\
begin\n\
predicates:\n  IsPairOf(m, a, b) <=> m = <a, b>\n\
macros:\n  tag(x) = <'t', x>, wrap(x, y) = tag(<x, y>)\n\
rule A:\n  [ In( <x, y> ) ] --[ A( wrap(x, y) ) ]-> [ Out( tag(x) ) ]\n\
rule B:\n  [ In( z ) ] --[ B( z ) ]-> [ ]\n\
lemma PlainLemma:\n  all-traces\n  \"All z #i. B( z ) @ #i ==> Ex #j. A( z ) @ #j\"\n\
lemma MacroLemma:\n  exists-trace\n  \"Ex x y m #i. A( m ) @ #i & IsPairOf(m, x, y) & m = wrap(x, y)\"\n\
end\n";

    /// HS `prettyLemma` quotes `fromMaybe expandedFormula ogFormula` on the
    /// header line and converts `expandedFormula` for the guarded block
    /// (lib/theory/src/Lemma.hs:121, :125), and `applyMacroInLemma` fills
    /// `ogFormula` with the pre-macro formula (lib/theory/src/Lemma.hs:83-88).
    /// So the macro call `wrap(x, y)` stands in the header and its expansion
    /// `<'t', x, y>` in the block, while the predicate atom `IsPairOf(m, x, y)`
    /// is inlined in both — parse-time expansion, which `liftedAddLemma` runs
    /// over the stored formula and its original alike
    /// (Theory/Text/Parser.hs:141-152).
    ///
    /// Expected strings are the pinned oracle's bytes for the fixture
    /// (`scripts/divergence_fixtures/expected/s3_macro_lemma_header.theory.hs.txt`).
    #[test]
    fn closed_lemma_header_uses_the_original_and_the_guarded_block_the_expanded() {
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let elaborated = crate::elaborate::elaborate(&parsed).expect("theory elaborates");
        let rendered: Vec<String> = parsed
            .items
            .iter()
            .filter_map(|item| match item {
                p::TheoryItem::Lemma(l) => render_parsed_lemma(l, &[], "", &elaborated),
                _ => None,
            })
            .collect();
        assert_eq!(
            rendered,
            vec![
                "lemma PlainLemma:\n  \
                 all-traces \"∀ z #i. (B( z ) @ #i) ⇒ (∃ #j. A( z ) @ #j)\"\n\
                 /*\nguarded formula characterizing all counter-examples:\n\
                 \"∃ z #i. (B( z ) @ #i) ∧ ∀ #j. (A( z ) @ #j) ⇒ ⊥\"\n*/\nby sorry",
                "lemma MacroLemma:\n  exists-trace\n  \
                 \"∃ x y m #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ∧ (m = wrap(x, y))\"\n\
                 /*\nguarded formula characterizing all satisfying traces:\n\
                 \"∃ x y m #i. (A( m ) @ #i) ∧ (m = <x, y>) ∧ (m = <'t', x, y>)\"\n*/\nby sorry",
            ]
        );
    }
}
