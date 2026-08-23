// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Export to other provers for the Tamarin prover (Rust port).
//!
//! Modules ported:
//! - [`proverif_header`] ← `ProVerifHeader` (header declarations for
//!   ProVerif output)
//!
//! `ProVerifHeader` is ported in full: all six constructors in the upstream
//! declaration order, which the derived `Ord` that `attribHeaders` and
//! `S.toList` rely on depends on.
//!
//! Not yet ported:
//! - `Export` (3819 lines — the ProVerif/ProVerif-equivalence/DeepSec
//!   exporters, i.e. `--output-module=proverif|proverifequiv|deepsec`)
//! - `RuleTranslation` (815 lines — multiset rewriting → process calculus
//!   translation)
//!
//! Blockers, in dependency order:
//! - Lemma and restriction formulas are stored as `tamarin_parser::ast::
//!   Formula`, not `LNFormula` (`tamarin_theory::theory::Lemma::formula`,
//!   `tamarin_theory::theory::OpenRestriction`).  The parser-AST →
//!   `SyntacticLNFormula` converter is `tamarin_theory::formula::from_parser`,
//!   but no stored field holds its result.  Export operates exclusively on
//!   `LNFormula`.
//! - There is no `prettyLNFormula` over `ProtoFormula`
//!   (`tamarin_theory::pretty_formula` renders the parser AST), yet Export
//!   emits rewritten `LNFormula`s verbatim inside comment blocks.
//! - `simplifyFormula` / `pnf` / `nnf` / `pullquants` / `prenex` /
//!   `shiftFreeIndices` are unported over `ProtoFormula`; `ppLemma`
//!   (Export.hs:1466) and `flattenNestedQuantifiers` (Export.hs:1517-1535)
//!   need them.
//! - About 1300 of Export.hs's lines (Export.hs:1705-2605 and :2922-3300) are
//!   Export-specific `LNFormula → LNFormula` transforms and shape classifiers
//!   with no analogue in the port.
//! - The typed OPEN theory is not retained as theory items:
//!   `TranslationElement::{Process, ProcessDef, FunctionTypingInfo,
//!   EquivLemma, DiffEquivLemma}` are never produced by elaboration, and
//!   `tamarin_sapic::apply` discards the typed process after MSR
//!   translation.  `tamarin_sapic::type_theory::type_theory_env` does port
//!   `Sapic.typeTheoryEnv` (Typing.hs:204-226) — the typed processes/defs
//!   including `typeAndRenameProcessDef`'s `_pVars` inference, the
//!   recomputed `function:` items, and the final `TypingEnvironment` whose
//!   `events` map `loadHeaders` (Export.hs:2743-2754) folds over to emit
//!   `event` headers — but it hands them back as a render-time overlay
//!   (`tamarin_theory::pretty_theory::TypedOverlay`), not as the
//!   `OpenTheory` value Export traverses (`processOpenTheory`,
//!   TheoryLoader.hs:481-483).
//!
//! Oracle-fixture reality at the pinned v1.13.0 (ef3f0468), measured over the
//! 1042-file corpus: `-m proverif` produces output for 44 files; `-m
//! proverifequiv` for those same 44, none of which contain an `equivLemma`, so
//! the equivalence path is unexercised; `-m deepsec` produces output for none,
//! since `prettyDeepSecHeader` (Export.hs:2818) rejects any equation including
//! the implicit `fst`/`snd`.  38 of the 123 process-bearing files — including
//! all 21 under `examples/sapic/export/` — die on `Non-exhaustive patterns in
//! function builtins`, because `builtins` (Export.hs:305-357) has no arm for
//! the `dest-*` or `natural-numbers` builtin names.

pub mod proverif_header;
