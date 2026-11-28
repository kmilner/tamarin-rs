// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of HS `renderGraphCode` (`imgThyPath`, Web/Theory.hs): turn a
//! system's DOT or JSON graph into an image with the configured command.
//!
//! HS names the files by a hash of the code under its cache directory and
//! reuses an image another request rendered; the port renders each request
//! in a private temporary directory of its own.

use std::ffi::OsStr;
use std::path::Path;

/// The graph code a render starts from: DOT text for `--with-dot`, the
/// system's JSON graph for `--with-json` (HS `ocFormat`).
pub(crate) enum GraphCode {
    Dot(String),
    Json(String),
}

/// HS `renderGraphCode`: write `code` to a graph file and convert it with
/// `cfg`'s command — `dot` (retried with `-Kfdp` when it fails) or the
/// `--with-json` command. `Ok(None)` after HS's `failed to convert` warning,
/// which the route answers with `notFound`; `Err` when the files cannot be
/// written or the command cannot be started, where HS raises.
pub(crate) fn render_graph_code(
    cfg: &crate::ServerConfig,
    code: GraphCode,
) -> Result<Option<Vec<u8>>, String> {
    // Private to this render (mode 0700 on Unix), so other users sharing the
    // temp directory can neither collide with nor read it; removed when it
    // goes out of scope.
    let mut builder = tempfile::Builder::new();
    builder.prefix("tamarin-rs-graph-");
    #[cfg(unix)]
    builder.permissions(std::os::unix::fs::PermissionsExt::from_mode(0o700));
    let dir = builder
        .tempdir()
        .map_err(|e| format!("could not create a graph directory: {e}"))?;
    let (ext, text) = match &code {
        GraphCode::Dot(text) => ("dot", text),
        GraphCode::Json(text) => ("json", text),
    };
    let graph_path = dir.path().join(format!("graph.{ext}"));
    let img_path = dir
        .path()
        .join(format!("graph.{ext}.{}", cfg.image_format.name()));
    let result = std::fs::write(&graph_path, text)
        .map_err(|e| format!("could not write {}: {e}", graph_path.display()))
        .and_then(|()| {
            let rendered = match &code {
                GraphCode::Dot(_) => {
                    dot_to_img(cfg, "dot", &graph_path, &img_path)?
                        || dot_to_img(cfg, "fdp", &graph_path, &img_path)?
                }
                GraphCode::Json(_) => {
                    let cmd = cfg.json_path.as_deref().unwrap_or("json");
                    run_converter(
                        "jsonToImg",
                        cmd,
                        &[img_path.as_os_str(), graph_path.as_os_str()],
                        &graph_path,
                    )?
                }
            };
            Ok(rendered.then(|| std::fs::read(&img_path).ok()).flatten())
        });
    if let Ok(None) = result {
        eprintln!("WARNING: failed to convert:\n  '{}'", graph_path.display());
    }
    result
}

/// HS `dotToImg`: `<dot> -T<format> -K<mode> -o <img> <graph>`.
fn dot_to_img(
    cfg: &crate::ServerConfig,
    mode: &str,
    graph: &Path,
    img: &Path,
) -> Result<bool, String> {
    let format = format!("-T{}", cfg.image_format.name());
    let layout = format!("-K{mode}");
    let args: [&OsStr; 5] = [
        format.as_ref(),
        layout.as_ref(),
        "-o".as_ref(),
        img.as_os_str(),
        graph.as_os_str(),
    ];
    run_converter("dotToImg", &cfg.dot_path, &args, graph)
}

/// HS `readProcessWithExitCode cmd args ""` in `dotToImg` / `jsonToImg`: run
/// with empty stdin, reporting a nonzero exit on stdout as `<who>: <cmd>
/// failed with code <i> for file <graph>:\n<err>`.
fn run_converter(who: &str, cmd: &str, args: &[&OsStr], graph: &Path) -> Result<bool, String> {
    let out = std::process::Command::new(cmd)
        .args(args)
        .stdin(std::process::Stdio::null())
        .output()
        .map_err(|e| format!("{cmd}: {e}"))?;
    if out.status.success() {
        return Ok(true);
    }
    println!(
        "{who}: {cmd} failed with code {} for file {}:\n{}",
        out.status.code().unwrap_or(-1),
        graph.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(false)
}
