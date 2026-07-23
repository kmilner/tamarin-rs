//! Tiny launcher: parse `-p <port>` then run [`tamarin_server::serve`].
//! Used by interactive UI debug sessions.

use std::net::SocketAddr;
use std::path::PathBuf;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let args: Vec<String> = std::env::args().collect();
    let mut port: u16 = 3001;
    let mut theories: Vec<PathBuf> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-p" | "--port" => {
                i += 1;
                port = args.get(i).expect("missing port arg").parse()?;
            }
            other => theories.push(PathBuf::from(other)),
        }
        i += 1;
    }

    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("info".parse().unwrap()),
        )
        .init();

    let data_dir = {
        let p = PathBuf::from("data");
        if p.is_dir() {
            p
        } else {
            PathBuf::from("../data")
        }
    };
    let frontend_dist = {
        let p = PathBuf::from("frontend/dist");
        if p.is_dir() {
            Some(p)
        } else {
            let p2 = PathBuf::from("../frontend/dist");
            if p2.is_dir() {
                Some(p2)
            } else {
                None
            }
        }
    };
    let maude_path = [
        "/usr/local/bin/maude",
        "/opt/homebrew/bin/maude",
        "/usr/bin/maude",
    ]
    .iter()
    .find(|p| std::path::Path::new(p).exists())
    .map(|s| s.to_string())
    .unwrap_or_else(|| "maude".into());

    let cfg = tamarin_server::ServerConfig {
        bind_addr: SocketAddr::from(([127, 0, 0, 1], port)),
        data_dir,
        frontend_dist,
        maude_path,
        max_steps: 500,
        derivcheck_timeout: 5,
        stop_on_trace: None,
    };
    tamarin_server::serve(cfg, theories).await
}
