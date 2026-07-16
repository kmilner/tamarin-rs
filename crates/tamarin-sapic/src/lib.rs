//! SAPIC process calculus for the Tamarin prover (Rust port).
//!
//! The data layer (Process, SapicAction, SapicLVar, ProcessParsedAnnotation,
//! ProcessPosition) lives in `tamarin_theory::sapic` because Haskell places
//! it under `lib/theory/src/Theory/Sapic/`. This crate hosts the
//! transformation passes from `lib/sapic/src/Sapic/`.
//!
//! Modules ported:
//! - [`bindings`] ← `Sapic.Bindings`
//! - [`annotation`] ← `Sapic.Annotation`
//! - [`secret_channels`] ← `Sapic.SecretChannels`
//! - [`facts`] ← `Sapic.Facts`
//! - [`typing`] ← `Sapic.Typing`
//! - [`locks`] ← `Sapic.Locks` (lock annotation; `checkLocks` not ported)
//! - [`inline`] ← process-call inlining (HS does this in the parser,
//!   `Theory.Text.Parser.Sapic.actionprocess`)
//! - [`let_destructors`] ← `Sapic.LetDestructors` (`let`-elimination /
//!   destructor-let annotation)
//! - [`base_translation`] ← `Sapic.Basetranslation`
//!   (linear + state + locks + `let` (FLet) + process-call marker)
//! - [`translate`] / [`apply`] ← top-level `Sapic`
//!
//! - [`states`] ← `Sapic.States` (pure-state / state-channel optimisation,
//!   gated on `options: translation-state-optimisation` / `_stateChannelOpt`)
//!
//! - [`warnings`] ← `Sapic.Warnings` (SAPIC-process wellformedness report;
//!   bound-twice / `WFBoundTwice` arm — `checkLocks` arm deferred)
//!
//! - [`report`] ← `Sapic.Report`
//! - [`secret_channels`]/`base_translation` — secret/private channels
//!   (`ChIn`/`ChOut` on a named/private channel)
//!
//! Not yet ported: `Sapic.Exceptions`.
//!
//! Also ported: [`progress_function`] ← `Sapic.ProgressFunction`,
//! [`progress_translation`] ← `Sapic.ProgressTranslation`,
//! [`reliable_channel`] ← `Sapic.ReliableChannelTranslation`,
//! [`compression`] ← `Sapic.Compression`.

pub mod annotation;
pub mod apply;
pub mod base_translation;
pub mod bindings;
pub mod compression;
pub mod convert;
pub mod facts;
pub mod inline;
pub mod let_destructors;
pub mod locks;
pub mod progress_function;
pub mod progress_translation;
pub mod reliable_channel;
pub mod report;
pub mod secret_channels;
pub mod states;
pub mod translate;
pub mod typing;
pub mod warnings;
