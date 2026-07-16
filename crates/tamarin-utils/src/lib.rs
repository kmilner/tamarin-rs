//! Utility library for the Tamarin prover (Rust port).
//!
//! Modules ported from `lib/utils/src/` of the upstream Haskell tree.
//!
//! Some modules mirror their upstream Haskell counterparts in full for
//! fidelity and are not all exercised by the prover itself (for example the
//! `env_tracer` and `timing` debug/diagnostic helpers). Their module docs
//! note when this is the case.

pub mod bind;
pub mod color;
pub mod cow;
pub mod dag;
pub mod dot;
/// The `env_gate!` macro is exported at the crate root via
/// `#[macro_export]`; this (private) module just holds its definition.
mod env_gate;
pub mod env_tracer;
pub mod fresh;
pub mod logic;
pub mod misc;
pub mod prelude_ext;
pub mod pretty;
pub mod pretty_html;
pub mod timing;
pub mod unicode;

/// Fast non-cryptographic hash map for internal *lookup-only* uses
/// (membership tests / order-independent grouping / memo caches).  Uses
/// `rustc_hash::FxBuildHasher`, which is `Default`, so this is a drop-in
/// replacement for `std::collections::HashMap` at call sites that never
/// iterate the map into observable output or into an ordering decision.
// FastMap definition site — the sanctioned std-map wrapper alias;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub type FastMap<K, V> = std::collections::HashMap<K, V, rustc_hash::FxBuildHasher>;
/// Fast non-cryptographic hash set — see [`FastMap`].
// FastSet definition site — the sanctioned std-set wrapper alias;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub type FastSet<K> = std::collections::HashSet<K, rustc_hash::FxBuildHasher>;

/// Hash one value with the same `FxBuildHasher` the [`FastMap`]/[`FastSet`]
/// aliases use.  For hash-prefilter patterns over deep ASTs: `Hash`/`Eq`
/// consistency guarantees equal values hash equal, so
/// `fx_hash_one(a) != fx_hash_one(b)` proves `a != b` and the deep equality
/// walk only runs on hash agreement.  The hash itself must never reach
/// observable output — it is a filter, not an ordering key.
pub fn fx_hash_one<T: std::hash::Hash + ?Sized>(value: &T) -> u64 {
    use std::hash::BuildHasher as _;
    rustc_hash::FxBuildHasher.hash_one(value)
}

/// Process-global monotone stamp source for the verified-identity
/// `subst_system` skip (see `constraint::solver::reduction`).
///
/// `next_stamp()` returns a globally-unique, strictly-increasing `u64`,
/// unique across threads AND `System` lineages (a `fetch_add` is monotone).
/// The value `0` is reserved as a sentinel that no `next_stamp()` ever
/// returns.  Stamps are only ever compared for **equality** with a value
/// copied into a same-thread `Cell`, so `Relaxed` ordering is correct: there
/// is no cross-thread happens-before requirement (each `System` is
/// thread-local — cloned by value at every proof fork, never shared `&`
/// across threads).  The atomic exists solely to guarantee global uniqueness,
/// so a grafted / replaced field can never coincidentally alias a stale,
/// unrelated stamp.  At 1 GHz it takes ~584 years to wrap.
#[inline]
pub fn next_stamp() -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static STAMP: AtomicU64 = AtomicU64::new(1);
    STAMP.fetch_add(1, Ordering::Relaxed)
}
