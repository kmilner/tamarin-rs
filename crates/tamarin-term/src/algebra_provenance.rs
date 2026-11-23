//! Which component produced each algebra answer of a session.
//!
//! The tallies measure how much of a run rests on a whole-command theorem.
//! Classification is conservative: an answer assembled in Rust from several
//! checked kernels counts as native Rust, not as proved.

use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Command {
    Unify,
    Match,
    Reduce,
    Variants,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Origin {
    /// One Lean export whose theorem covers the whole command without an
    /// unchecked premise about the theory. The export either computed the
    /// answer or accepted the answer of an unverified solver as a certificate
    /// for the whole command.
    Proved,
    /// One Lean export whose theorem assumes the rule table is convergent
    /// with the finite variant property, on a table the certifier did not
    /// accept. Maude makes the same assumption.
    Assumed,
    /// Native-only answers that no single theorem covers: Rust that combines
    /// several checked kernels (the tuple unpacker with a total export).
    /// No family of variants has this origin: one that a Rust solver
    /// proposed is used only after the certificate checker accepted it.
    NativeRust,
    /// Rust that every backend runs before consulting an algebra engine:
    /// free unification, the normal-form check and syntactic shortcuts.
    SharedRust,
    Maude,
}

/// How native-only obtained a family of variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantRoute {
    /// A specialised Rust solver proposed the family and the certificate
    /// checker accepted it.
    Proposer,
    /// The bounded narrowing search of the Lean library
    /// (`tamarin_checked_variants`) proposed the family and the certificate
    /// checker accepted it.
    CheckedExport,
    /// The folding export proposed the family and the certificate checker
    /// accepted it.
    GeneralExport,
}

const COMMANDS: usize = 4;
const ORIGINS: usize = 5;
const ROUTES: usize = 3;

/// Fresh answers and cache hits, by command and by the origin of the answer.
#[derive(Default)]
pub struct Provenance {
    fresh: [[AtomicU64; ORIGINS]; COMMANDS],
    cached: [[AtomicU64; ORIGINS]; COMMANDS],
    routes: [AtomicU64; ROUTES],
}

/// A copy of the tallies: `[command][origin]`, in declaration order.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProvenanceSnapshot {
    pub fresh: [[u64; ORIGINS]; COMMANDS],
    pub cached: [[u64; ORIGINS]; COMMANDS],
}

impl ProvenanceSnapshot {
    pub fn fresh(&self, command: Command, origin: Origin) -> u64 {
        self.fresh[command as usize][origin as usize]
    }

    pub fn cached(&self, command: Command, origin: Origin) -> u64 {
        self.cached[command as usize][origin as usize]
    }

    /// Every answer of `command`, fresh or cached.
    pub fn total(&self, command: Command) -> u64 {
        let row = command as usize;
        self.fresh[row].iter().sum::<u64>() + self.cached[row].iter().sum::<u64>()
    }
}

impl Provenance {
    pub(crate) fn record(&self, command: Command, origin: Origin) {
        self.fresh[command as usize][origin as usize].fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn record_cached(&self, command: Command, origin: Origin) {
        self.cached[command as usize][origin as usize].fetch_add(1, Ordering::Relaxed);
    }

    #[cfg(feature = "lean-unification")]
    pub(crate) fn record_route(&self, route: VariantRoute) {
        self.routes[route as usize].fetch_add(1, Ordering::Relaxed);
    }

    /// The families of variants native-only obtained by `route`.
    pub fn route(&self, route: VariantRoute) -> u64 {
        self.routes[route as usize].load(Ordering::Relaxed)
    }

    pub fn snapshot(&self) -> ProvenanceSnapshot {
        let read = |table: &[[AtomicU64; ORIGINS]; COMMANDS]| {
            let mut out = [[0; ORIGINS]; COMMANDS];
            for (row, cells) in out.iter_mut().zip(table) {
                for (cell, count) in row.iter_mut().zip(cells) {
                    *cell = count.load(Ordering::Relaxed);
                }
            }
            out
        };
        ProvenanceSnapshot {
            fresh: read(&self.fresh),
            cached: read(&self.cached),
        }
    }

    /// One line per command that answered anything, for `TAM_MAUDE_CACHE_STATS`.
    pub(crate) fn report(&self) -> Vec<String> {
        let snapshot = self.snapshot();
        let names = ["proved", "assumed", "native_rust", "shared_rust", "maude"];
        let row = |cells: &[u64; ORIGINS]| {
            names
                .iter()
                .zip(cells)
                .map(|(name, count)| format!("{name}={count}"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        ["unify", "match", "reduce", "variants"]
            .iter()
            .enumerate()
            .filter(|(i, _)| {
                snapshot.fresh[*i]
                    .iter()
                    .chain(&snapshot.cached[*i])
                    .any(|n| *n != 0)
            })
            .map(|(i, command)| {
                format!(
                    "[ALGEBRA_PROVENANCE] {command} fresh: {} | cached: {}",
                    row(&snapshot.fresh[i]),
                    row(&snapshot.cached[i])
                )
            })
            .chain(
                self.routes
                    .iter()
                    .any(|n| n.load(Ordering::Relaxed) != 0)
                    .then(|| {
                        format!(
                            "[VARIANT_ROUTES] proposer={} checked_export={} general_export={}",
                            self.route(VariantRoute::Proposer),
                            self.route(VariantRoute::CheckedExport),
                            self.route(VariantRoute::GeneralExport),
                        )
                    }),
            )
            .collect()
    }
}
