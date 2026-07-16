//! Export to other provers for the Tamarin prover (Rust port).
//!
//! Modules ported:
//! - [`proverif_header`] ← `ProVerifHeader` (header declarations for
//!   ProVerif output)
//!
//! Not yet ported:
//! - `Export` (~2100 lines — main ProVerif/DeepSec exporters)
//! - `RuleTranslation` (~600 lines — multiset rewriting → process
//!   calculus translation)
//!
//! Both depend heavily on `tamarin-theory` and `tamarin-sapic`, which
//! still have substantial work remaining.

pub mod proverif_header;
