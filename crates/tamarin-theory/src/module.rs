// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Module` — the `--output-module` / `-m` selector.
//!
//! HS `ModuleType` (Theory/Module.hs:16-25) derives `Enum`/`Bounded`, and
//! `moduleList` (Batch.hs:82-84) renders `[minBound ..]` with `show` to build
//! the flag's placeholder `spthytyped|spthy|msr|proverifequiv|proverif|deepsec`.
//! The declaration order is load-bearing twice over: it fixes that placeholder
//! and, per the upstream comment (Theory/Module.hs:17-19), keeps no `show`
//! value a prefix of a later one.

use std::fmt;
use std::str::FromStr;

/// HS `ModuleType` (Theory/Module.hs:16-25).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ModuleType {
    /// `spthytyped` — spthy with the SAPIC type inference applied.
    SpthyTyped,
    /// `spthy` — the source theory, untranslated.
    Spthy,
    /// `msr` — pure multiset rewriting, after the SAPIC translation.
    Msr,
    /// `proverifequiv` — ProVerif export for the equivalence lemmas.
    ProVerifEquivalence,
    /// `proverif` — ProVerif export for the reachability lemmas.
    ProVerif,
    /// `deepsec` — DeepSec export for the equivalence lemmas.
    DeepSec,
}

impl ModuleType {
    /// HS `[minBound ..] :: [ModuleType]` (Batch.hs:82).
    pub const ALL: [ModuleType; 6] = [
        ModuleType::SpthyTyped,
        ModuleType::Spthy,
        ModuleType::Msr,
        ModuleType::ProVerifEquivalence,
        ModuleType::ProVerif,
        ModuleType::DeepSec,
    ];

    /// HS `show` (Theory/Module.hs:27-33).
    pub fn as_str(self) -> &'static str {
        match self {
            ModuleType::SpthyTyped => "spthytyped",
            ModuleType::Spthy => "spthy",
            ModuleType::Msr => "msr",
            ModuleType::ProVerifEquivalence => "proverifequiv",
            ModuleType::ProVerif => "proverif",
            ModuleType::DeepSec => "deepsec",
        }
    }

    /// HS `description` (Theory/Module.hs:35-41), used to build the flag's
    /// help text (`moduleDescriptions`, Batch.hs:84).
    pub fn description(self) -> &'static str {
        match self {
            ModuleType::SpthyTyped => "spthy with explicit types inferred",
            ModuleType::Spthy => "spthy (including Sapic Processes)",
            ModuleType::Msr => "pure msrs (with Sapic translation)",
            ModuleType::ProVerifEquivalence => "ProVerif export for the equivalence lemmas",
            ModuleType::ProVerif => "ProVerif export for the reachability lemmas",
            ModuleType::DeepSec => "DeepSec export for the equivalences lemmas",
        }
    }

    /// HS `find ((str ==) . show) [minBound ..]` (TheoryLoader.hs:373-376):
    /// exact match against the `show` strings, no prefixes and no aliases.
    /// `None` is HS's `ArgumentError "output mode not supported."`.
    pub fn from_show(s: &str) -> Option<ModuleType> {
        ModuleType::ALL.into_iter().find(|m| m.as_str() == s)
    }

    /// HS `moduleList` (Batch.hs:83) — the `-m` placeholder text.
    pub fn module_list() -> String {
        ModuleType::ALL
            .iter()
            .map(|m| m.as_str())
            .collect::<Vec<_>>()
            .join("|")
    }
}

impl fmt::Display for ModuleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for ModuleType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, ()> {
        ModuleType::from_show(s).ok_or(())
    }
}

#[cfg(test)]
mod tests {
    use super::ModuleType;

    #[test]
    fn show_strings_match_hs() {
        assert_eq!(
            ModuleType::ALL.map(|m| m.as_str()),
            [
                "spthytyped",
                "spthy",
                "msr",
                "proverifequiv",
                "proverif",
                "deepsec"
            ]
        );
    }

    #[test]
    fn module_list_matches_hs_placeholder() {
        assert_eq!(
            ModuleType::module_list(),
            "spthytyped|spthy|msr|proverifequiv|proverif|deepsec"
        );
    }

    #[test]
    fn parse_roundtrips_and_rejects_unknown() {
        for m in ModuleType::ALL {
            assert_eq!(ModuleType::from_show(m.as_str()), Some(m));
        }
        assert_eq!(ModuleType::from_show(""), None);
        assert_eq!(ModuleType::from_show("bogus"), None);
        // Prefixes and case variants are not accepted: HS compares with `==`.
        assert_eq!(ModuleType::from_show("spthyt"), None);
        assert_eq!(ModuleType::from_show("SPTHY"), None);
    }

    #[test]
    fn no_show_value_is_a_prefix_of_a_later_one() {
        // The invariant the upstream declaration order documents
        // (Theory/Module.hs:17-19).
        for (i, a) in ModuleType::ALL.iter().enumerate() {
            for b in &ModuleType::ALL[i + 1..] {
                assert!(
                    !b.as_str().starts_with(a.as_str()),
                    "{} is a prefix of the later {}",
                    a,
                    b
                );
            }
        }
    }
}
