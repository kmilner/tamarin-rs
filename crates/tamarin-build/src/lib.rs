//! Build dependency shared by crates that embed upstream files. Cargo runs our
//! bootstrap before either consumer's build script, even in a parallel build.

pub const UPSTREAM_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tamarin-prover");
