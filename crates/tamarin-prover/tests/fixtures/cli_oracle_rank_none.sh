#!/bin/sh
# Deterministic test oracle for the `--oracle-only` pin in tests/cli_e2e.rs:
# it ranks NOTHING.
#
# That is the exact input `--oracle-only` reacts to — HS `oracleRanking`
# (ProofMethod.hs:604-620) returns `Just ApplySorry` when `quitOnEmpty` is set,
# the goal list was non-empty and the oracle named none of it, so the proof
# stops at a `sorry` instead of falling through to the unranked goals.  Running
# the same script WITHOUT `--oracle-only` therefore has to reach a different
# result, which is what makes the pair non-vacuous.
#
# Draining stdin is required: HS `readProcess` writes the whole goal list, and
# a script that exits without reading it would race with the writer.
cat >/dev/null
exit 0
