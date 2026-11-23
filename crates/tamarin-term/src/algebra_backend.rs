//! Selection of the algebra backend: Maude, or the in-process Lean library.
//!
//! Native-only starts no Maude process. Its unifier, matcher and normalizer
//! are Lean exports that carry whole-command theorems, and it uses a family
//! of variants only after the Lean certificate checker accepted it. The Rust
//! encoding of requests and replies and the C/Lean runtime boundary remain
//! trusted code.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlgebraBackend {
    Maude,
    NativeOnly,
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
        self != Self::NativeOnly
    }

    pub fn validate(self) -> Result<(), String> {
        if self == Self::NativeOnly {
            if !cfg!(feature = "lean-unification") {
                return Err("native-only requires a build with --features lean-unification".into());
            }
            // The oracle compares a normal-form shortcut with Maude's reply.
            let name = "TAM_RS_VERIFY_REDUCE_NF";
            if std::env::var_os(name).is_some() {
                return Err(format!("native-only is incompatible with {name}; unset it"));
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
            _ => Err(format!("unknown algebra backend: {value}")),
        }
    }
}

/// What a native-only run tells the user, once per theory, when its results
/// rest on a rewrite table the Lean certifier did not accept. The wording is
/// stable: tests and scripts match on it. See
/// [`crate::maude_proc::MaudeHandle::convergence_assumed`].
pub const ASSUMED_CONVERGENT_NOTICE: &str =
    "the equational theory's convergence was not certified by the proved checker; \
     results assume the user-specified equations are convergent, \
     as Maude-based Tamarin also assumes";
