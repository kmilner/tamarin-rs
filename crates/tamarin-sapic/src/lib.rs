//! SAPIC process calculus for the Tamarin prover (Rust port).
//!
//! The data layer (Process, SapicAction, SapicLVar, ProcessParsedAnnotation,
//! ProcessPosition) lives in `tamarin_theory::sapic` because Haskell places
//! it under `lib/theory/src/Theory/Sapic/`. This crate hosts the
//! transformation passes from `lib/sapic/src/Sapic/`.
//!
//! Modules ported:
//! - [`annotation`] ← `Sapic.Annotation`
//! - [`base_translation`] ← `Sapic.Basetranslation`
//! - [`bindings`] ← `Sapic.Bindings`
//! - [`compression`] ← `Sapic.Compression`
//! - [`facts`] ← `Sapic.Facts`
//! - [`let_destructors`] ← `Sapic.LetDestructors`
//! - [`locks`] ← `Sapic.Locks` (lock annotation; `checkLocks` not ported)
//! - [`progress_function`] ← `Sapic.ProgressFunction`
//! - [`progress_translation`] ← `Sapic.ProgressTranslation`
//! - [`reliable_channel`] ← `Sapic.ReliableChannelTranslation`
//! - [`report`] ← `Sapic.Report`
//! - [`secret_channels`] ← `Sapic.SecretChannels`
//! - [`states`] ← `Sapic.States` (pure-state / state-channel optimisation,
//!   gated on `options: translation-state-optimisation` / `_stateChannelOpt`)
//! - [`translate`] / [`apply`] ← top-level `Sapic`
//! - [`typing`] / [`type_theory`] ← `Sapic.Typing`
//! - [`warnings`] ← `Sapic.Warnings` (SAPIC-process wellformedness report;
//!   bound-twice / `WFBoundTwice` arm — `checkLocks` arm deferred)
//!
//! The parser-AST → `PlainProcess` conversion, with the process-call
//! inlining HS performs in its parser, lives in
//! `tamarin_theory::{process_convert, process_inline}` beside the data layer.
//!
//! Not yet ported: `Sapic.Exceptions`.

pub mod annotation;
pub mod apply;
pub mod base_translation;
pub mod bindings;
pub mod compression;
pub mod facts;
pub mod let_destructors;
pub mod locks;
pub mod progress_function;
pub mod progress_translation;
pub mod reliable_channel;
pub mod report;
pub mod secret_channels;
pub mod states;
pub mod translate;
pub mod type_theory;
pub mod typing;
pub mod warnings;
