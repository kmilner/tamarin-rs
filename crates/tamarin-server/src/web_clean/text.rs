//! Plain-text (`text/plain`) response bodies.
//!
//! Observed `kind=text` routes:
//! * `source` and `message` — identical: the pretty-printed theory source (the
//!   prover's output verbatim; no trailing newline in the response body). The
//!   web layer is a pass-through, so [`source_body`] is the identity.
//! * `next/<mode>/proof/<lemma>` and `prev/<mode>/proof/<lemma>` — a single URL
//!   path string naming where the client should navigate (resolved numeric
//!   index), e.g. `/thy/trace/1/main/proof/unforgeability`. Also a pass-through
//!   of a value the prover computes; [`nav_target`] is the identity.

/// The `source` / `message` text body: the theory source, returned verbatim.
pub fn source_body(theory_source: &str) -> &str {
    theory_source
}

/// The `next` / `prev` navigation body: a target URL path, returned verbatim.
pub fn nav_target(path: &str) -> &str {
    path
}

/// Build a `main/proof` navigation target path.
pub fn main_proof_path(index: u64, lemma: &str, proof_path: &[&str]) -> String {
    let mut s = format!("/thy/trace/{index}/main/proof/{lemma}");
    for seg in proof_path {
        s.push('/');
        s.push_str(seg);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nav_path_builder() {
        assert_eq!(
            main_proof_path(1, "unforgeability", &[]),
            "/thy/trace/1/main/proof/unforgeability"
        );
        assert_eq!(
            main_proof_path(3, "exec", &["_", "B_2"]),
            "/thy/trace/3/main/proof/exec/_/B_2"
        );
    }
}
