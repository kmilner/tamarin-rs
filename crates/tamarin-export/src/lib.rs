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
//! The formula surface Export reads is ported: `tamarin_theory::theory::Lemma`'s
//! `formula` / `original_formula` and `tamarin_theory::restriction::Restriction`
//! carry `LNFormula`, as HS's `ProtoLemma LNFormula` (Items/LemmaItem.hs:53-54)
//! and `ProtoRestriction LNFormula` (Theory/Model/Restriction.hs:70) do, and
//! `tamarin_theory::pretty_formula::lnformula_doc` is `prettyLNFormula`
//! (Theory/Model/Formula.hs:518-520), the renderer of the formulas Export puts
//! inside its comment blocks (Export.hs:1424-1425).
//!
//! Blockers, in dependency order:
//! - `nnf` / `pullquants` / `prenex` / `pnf`
//!   (Theory/Model/Formula.hs:415-456) are unported over `ProtoFormula`;
//!   `ppLemma` (Export.hs:1462-1469#ppLemma, see line 1469) and
//!   `flattenNestedQuantifiers` (Export.hs:1517-1535) need them beside
//!   `tamarin_theory::formula::shift_free_indices` and the `simplifyFormula`
//!   that `tamarin_accountability::generation` keeps private to that crate.
//! - About 1300 of Export.hs's lines (Export.hs:1705-2605 and :2922-3300) are
//!   Export-specific `LNFormula → LNFormula` transforms and shape classifiers
//!   with no analogue in the port.
//! - Export's traversal of the typed OPEN theory is unported.  The theory
//!   itself is there: elaboration builds the
//!   `TranslationElement::{Process, ProcessDef, FunctionTypingInfo,
//!   EquivLemma, DiffEquivLemma}` items, and
//!   `tamarin_sapic::type_theory::type_theory_env` ports `Sapic.typeTheoryEnv`
//!   (Typing.hs:204-226) — it rewrites those items with the typed
//!   processes/defs, including `typeAndRenameProcessDef`'s `_pVars` inference
//!   and the recomputed `function:` items, and returns the
//!   `TypingEnvironment` whose `events` map `loadHeaders`
//!   (Export.hs:2743-2754) folds over to emit `event` headers.  What has no
//!   port is what `processOpenTheory` (TheoryLoader.hs:481-483) hands that
//!   theory to.
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
