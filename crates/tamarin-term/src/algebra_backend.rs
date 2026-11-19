//! Selection of the experimental algebra backend. Native-only means no Maude
//! process, not that all existing Rust fast paths are formally verified.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlgebraBackend {
    Maude,
    Hybrid,
    NativeOnly,
}

impl Default for AlgebraBackend {
    fn default() -> Self {
        if cfg!(feature = "lean-unification") {
            Self::Hybrid
        } else {
            Self::Maude
        }
    }
}

impl AlgebraBackend {
    pub fn uses_maude(self) -> bool {
        self != Self::NativeOnly
    }

    pub fn validate(self) -> Result<(), String> {
        if self != Self::Maude && !cfg!(feature = "lean-unification") {
            return Err(
                "hybrid and native-only require a build with --features lean-unification".into(),
            );
        }
        if self == Self::NativeOnly {
            for name in [
                "TAM_RS_NO_LEAN_UNIFY",
                "TAM_RS_VERIFY_LEAN_UNIFY",
                "TAM_RS_VERIFY_REDUCE_NF",
            ] {
                if std::env::var_os(name).is_some() {
                    return Err(format!("native-only is incompatible with {name}; unset it"));
                }
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
            "hybrid" => Ok(Self::Hybrid),
            "native-only" => Ok(Self::NativeOnly),
            _ => Err(format!("unknown algebra backend: {value}")),
        }
    }
}
