// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of Haskell's `dotToImg` (Web/Theory.hs:1494-1497) — shell out to the
//! GraphViz binary to turn a rendered DOT document into an image.
//!
//! The DOT document itself is produced by
//! [`tamarin_theory::constraint::system::dot`] (HS
//! `Theory.Constraint.System.Dot`), which the batch `--output-dot` writer
//! shares; only the process spawning is web-side, exactly as in Haskell.

use tamarin_theory::constraint::system::dot::system_to_dot_with;
use tamarin_theory::constraint::system::graph::GraphOptions;
use tamarin_theory::constraint::system::System;

/// Helper used by handlers to render the [`System`] as DOT and pipe it
/// through `<dot_cmd> -Tsvg` under the given graph options.  `dot_cmd` is
/// HS `dotPath` (Environment.hs:37-38): the `--with-dot` value, or the bare
/// `"dot"` resolved via `$PATH`.  Returns the SVG bytes on success.  When
/// `dot` is missing or fails, returns the DOT source instead (the frontend's
/// `intdot-staticgraph` can render DOT client-side via viz.js, so this
/// stays a useful response).
pub fn render_svg_or_dot_with(sys: &System, opts: &GraphOptions, dot_cmd: &str) -> RenderResult {
    let dot = system_to_dot_with(sys, opts);
    match try_render_dot_to_svg(&dot, dot_cmd) {
        Ok(svg) => RenderResult::Svg(svg),
        Err(_) => RenderResult::Dot(dot),
    }
}

/// What we got back from `dot`.
pub enum RenderResult {
    /// SVG bytes produced by `dot -Tsvg`.
    Svg(Vec<u8>),
    /// Raw DOT source, returned when the `dot` binary is unavailable or failed.
    Dot(String),
}

fn try_render_dot_to_svg(dot: &str, dot_cmd: &str) -> std::io::Result<Vec<u8>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new(dot_cmd)
        .args(["-Tsvg"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    // Write the full DOT to `dot`'s stdin on a separate thread while the
    // main thread drains stdout/stderr via `wait_with_output`.  Doing the
    // (blocking) `write_all` inline before reading stdout can deadlock on
    // large graphs: `dot` fills its stdout pipe and blocks, and so does our
    // `write_all` on a full stdin pipe.
    let writer = child.stdin.take().map(|mut sin| {
        let bytes = dot.as_bytes().to_vec();
        std::thread::spawn(move || sin.write_all(&bytes))
    });
    let out = child.wait_with_output()?;
    if let Some(handle) = writer {
        // Propagate any write error (ignore a panicked thread).
        if let Ok(res) = handle.join() {
            res?;
        }
    }
    if !out.status.success() {
        return Err(std::io::Error::other(format!(
            "dot exited with status {:?}",
            out.status
        )));
    }
    Ok(out.stdout)
}
