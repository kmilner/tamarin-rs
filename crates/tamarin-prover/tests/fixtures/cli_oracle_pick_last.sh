#!/bin/sh
# Deterministic test oracle for the `--oraclename` pin in tests/cli_e2e.rs.
#
# Contract (HS `oracleRanking`, ProofMethod.hs:604-620): argv[1] is the lemma
# name, stdin carries one `<index>: <goal>` line per open goal, and stdout is
# the list of indices to rank FIRST — anything not named keeps its incoming
# order behind them.  This one ranks the LAST goal first, which is a different
# order from every built-in ranking, so a run that never consulted the oracle
# cannot produce the pinned bytes.
#
# It must drain stdin (HS `readProcess` writes the whole goal list before it
# reads), and it must be byte-deterministic: no timestamps, no $RANDOM, no
# environment reads.
last=''
while IFS= read -r line; do
    case "$line" in
        [0-9]*) last="${line%%:*}" ;;
    esac
done
[ -n "$last" ] && echo "$last"
exit 0
