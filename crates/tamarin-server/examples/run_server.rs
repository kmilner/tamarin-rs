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

    let first_dir = |candidates: [&str; 2]| {
        candidates
            .into_iter()
            .map(PathBuf::from)
            .find(|p| p.is_dir())
    };
    let data_dir = first_dir(["data", "../data"]).unwrap_or_else(|| PathBuf::from("../data"));
    let frontend_dist = first_dir(["frontend/dist", "../frontend/dist"]);
    let maude_path = tamarin_test_support::maude_path().unwrap_or_else(|| "maude".into());

    let cfg = tamarin_server::ServerConfig {
        bind_addr: SocketAddr::from(([127, 0, 0, 1], port)),
        data_dir,
        frontend_dist,
        maude_path,
        derivcheck_timeout: 5,
        solver_parameters: Default::default(),
        stop_on_trace: None,
        dot_path: "dot".to_string(),
        json_path: None,
        theory_load: Default::default(),
    };
    tamarin_server::serve(cfg, theories).await
}
