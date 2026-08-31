//! One integration-test process for every whole-corpus structural audit. The
//! modules share `corpus_util`'s single-flight parsed/elaborated theory cache.

mod corpus_util;
#[path = "corpus_audits/guarded_payload_census.rs"]
mod guarded_payload_census;
#[path = "corpus_audits/s3_translated_theory_probes.rs"]
mod s3_translated_theory_probes;
