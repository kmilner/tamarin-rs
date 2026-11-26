//! Selection of the algebra backend: Maude, or the in-process Lean library.
//!
//! Native-only starts no Maude process. Its unifier, matcher and normalizer
//! are Lean exports that carry whole-command theorems, and it uses a family
//! of variants only after the Lean certificate checker accepted it. The Rust
//! encoding of requests and replies and the C/Lean runtime boundary remain
//! trusted code.
//!
//! Native starts no Maude process either. It runs the code of the Maude
//! backend, whose Rust front ends answer most requests, and hands each
//! request that backend would send to Maude to the Lean library instead:
//! the unifier, matcher, normalizer and variant checker native-only uses.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlgebraBackend {
    Maude,
    NativeOnly,
    /// The Maude backend's code with every Maude request handed to the
    /// proved Lean exports.
    Native,
}

/// Maude is the default in every build. Native-only does not yet finish every
/// theory, so it remains an explicit opt-in.
impl Default for AlgebraBackend {
    fn default() -> Self {
        Self::Maude
    }
}

impl AlgebraBackend {
    pub fn uses_maude(self) -> bool {
        self == Self::Maude
    }

    /// The value of `--algebra-backend` that selects this backend.
    pub fn name(self) -> &'static str {
        match self {
            Self::Maude => "maude",
            Self::NativeOnly => "native-only",
            Self::Native => "native",
        }
    }

    pub fn validate(self) -> Result<(), String> {
        if !self.uses_maude() {
            if !cfg!(feature = "lean-unification") {
                let name = self.name();
                return Err(format!(
                    "{name} requires a build with --features lean-unification"
                ));
            }
            // The oracle compares a normal-form shortcut with Maude's reply.
            let name = "TAM_RS_VERIFY_REDUCE_NF";
            if std::env::var_os(name).is_some() {
                let backend = self.name();
                return Err(format!("{backend} is incompatible with {name}; unset it"));
            }
        }
        Ok(())
    }
}

impl std::str::FromStr for AlgebraBackend {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "maude" => Ok(Self::Maude),
            "native-only" => Ok(Self::NativeOnly),
            "native" => Ok(Self::Native),
            _ => Err(format!("unknown algebra backend: {value}")),
        }
    }
}

/// What a run on a native backend tells the user, once per theory, when its results
/// rest on a rewrite table the Lean certifier did not accept. The wording is
/// stable: tests and scripts match on it. See
/// [`crate::maude_proc::MaudeHandle::convergence_assumed`].
pub const ASSUMED_CONVERGENT_NOTICE: &str =
    "the equational theory's convergence was not certified by the proved checker; \
     results assume the user-specified equations are convergent, \
     as Maude-based Tamarin also assumes";
