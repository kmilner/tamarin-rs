// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins the `tamarin-prover variants` block against the oracle.
//!
//! HS `Main.Mode.Intruder.run` (Main/Mode/Intruder.hs:43-63) generates the
//! Diffie-Hellman and the bilinear-pairing intruder rules through two
//! separate maude handles and prints `putStrLn (dhS ++ bpS)`, where each
//! block is `renderDoc . prettyIntruderVariants`
//! (Theory/Model/Rule.hs:1464-1466).  `pretty_intruder_variants` is that
//! renderer, and the rule bodies come out of `rule::pretty_rule_restr_gen`
//! over `LNFact`s whose arguments are breakable term Docs, as HS's are.
//!
//! No gate on this branch runs `tamarin-prover variants`
//! (`crates/tamarin-prover/tests/probe_reports.rs` covers only the failure
//! path of the subcommand), so this file is the byte contract for the
//! subcommand's stdout.  The expected bytes and their provenance live in
//! `tests/assets/intruder_variants.expected`.

use std::path::{Path, PathBuf};

use tamarin_theory::intruder_rules::{bp_intruder_rules, dh_intruder_rules};
use tamarin_theory::pretty_formula::pretty_intruder_variants;

/// Absolute maude locations probed before `PATH` is walked.
///
/// This probe mirrors the crate-shared `src/test_maude.rs` one (an
/// integration test cannot see a `#[cfg(test)]` module of the library it
/// links) — keep the two in sync.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Last resort, after `PATH`: the linuxbrew prefix this project's maude lives
/// under on the development box, which is deliberately not on `PATH`.
const MAUDE_LINUXBREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The maude the case below runs against: `$MAUDE_PATH`, else the first
/// existing [`MAUDE_CANDIDATES`] entry, else a `PATH` walk, else
/// [`MAUDE_LINUXBREW`].
///
/// Resolving NOTHING is a misconfiguration, not a reason to skip: the case
/// opens with `let mp = match maude_path() { Some(p) => p, None => return }`,
/// so a `None` here reports the same green run with and without maude
/// installed.  Panic instead — unless `TAM_ALLOW_NO_MAUDE=1` explicitly asks
/// for the silent skip (a box that genuinely has no maude).  A `MAUDE_PATH`
/// naming a file that does not exist is the same misconfiguration and panics
/// too.
fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?} / PATH / {MAUDE_LINUXBREW}, or point it at a \
             real maude — skipping every maude-gated case here would report \
             green vacuously"
        );
        return Some(p);
    }
    if let Some(c) = MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
    {
        return Some((*c).to_string());
    }
    // `PATH` walk, kept dependency-free like every other copy of this probe.
    if let Some(p) = std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|d| d.join("maude"))
            .find(|p| p.is_file())
    }) {
        return Some(p.to_string_lossy().into_owned());
    }
    if std::path::Path::new(MAUDE_LINUXBREW).exists() {
        return Some(MAUDE_LINUXBREW.to_string());
    }
    if std::env::var("TAM_ALLOW_NO_MAUDE").as_deref() == Ok("1") {
        return None;
    }
    panic!(
        "no maude found: MAUDE_PATH unset, none of {MAUDE_CANDIDATES:?} exist, \
         nothing named `maude` on PATH, and no {MAUDE_LINUXBREW}. Every \
         maude-gated case in this file would skip and the run would be green \
         having proved nothing. Install maude, set MAUDE_PATH, or set \
         TAM_ALLOW_NO_MAUDE=1 to accept the silent skip."
    );
}

/// The expected bytes: the asset minus its leading `//` provenance header.
fn expected() -> String {
    let path: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/assets/intruder_variants.expected");
    let text = std::fs::read_to_string(&path).expect("read the expected intruder-variants block");
    let body: String = text
        .split_inclusive('\n')
        .skip_while(|l| l.starts_with("//"))
        .collect();
    assert!(
        body.starts_with("rule (modulo AC) c_exp:"),
        "the header strip left {:?}: the asset's `//` provenance header must \
         run to the first rule and no further",
        &body[..body.len().min(60)]
    );
    body
}

/// The subcommand's whole stdout, byte for byte.
///
/// HS starts one maude on `dhMaudeSig` and a second on `bpMaudeSig`
/// (Main/Mode/Intruder.hs:44-53) and passes `False` for the diff flag in both
/// generators.  The two blocks abut with no separating newline, and
/// `putStrLn` adds the single trailing one.
#[test]
fn variants_stdout_matches_the_oracle_bytes() {
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let start = |sig| {
        tamarin_term::maude_proc::MaudeHandle::start(&mp, sig)
            .unwrap_or_else(|e| panic!("maude at {mp} failed to start: {e:?}"))
    };
    let dh = start(tamarin_term::maude_sig::dh_maude_sig());
    let dh_s = pretty_intruder_variants(&dh_intruder_rules(false, &dh));
    let bp = start(tamarin_term::maude_sig::bp_maude_sig());
    let bp_s = pretty_intruder_variants(&bp_intruder_rules(false, &bp));

    let got = format!("{dh_s}{bp_s}\n");
    let want = expected();
    if got != want {
        let first = got
            .lines()
            .zip(want.lines())
            .position(|(g, w)| g != w)
            .unwrap_or(got.lines().count().min(want.lines().count()));
        panic!(
            "`variants` stdout left the oracle bytes at line {}:\n  got  {:?}\n  want {:?}",
            first + 1,
            got.lines().nth(first),
            want.lines().nth(first)
        );
    }
}
