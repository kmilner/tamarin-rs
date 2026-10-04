#!/usr/bin/env bash
# Public entry point; the gate implementations own comparison/cache policy.
set -uo pipefail
# A user interruption must not advance `all` to the next expensive suite.
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
    cat <<'EOF'
Usage: scripts/test.sh {proof|web|all|harness}

  proof    Run the 505-theory proof corpus (fills/reuses the Haskell cache).
  web      Run the 77-theory web corpus (fills/reuses the Haskell cache).
  all      Run both, sequentially; report failure if either fails.
  harness  Run the cache/comparison harness regression tests.

Prepare first: ./setup.sh testing && cargo build --release -p tamarin-prover
There is no separate cache-generation step: cold runs fill, warm runs reuse.
This entry point never rebuilds binaries or deletes caches.

Each corpus invocation saves run.log, results.tsv and exit-code under a fresh
scripts/results/<suite>.* directory (override parent with RESULTS_ROOT).
Web diagnostic files are saved there under diffs/.

Overrides: ALLOWLIST=<file> (single suite only), JOBS, FILE_TIMEOUT, HS_N,
HS_PATH, RS_PATH, MAUDE_PATH, TAMARIN_RS_CACHE_ROOT and other gate settings.
Defaults: FILE_TIMEOUT=600; proof JOBS=2, HS_N=4; web JOBS=1.
For a quick web smoke test: ALLOWLIST=seed scripts/test.sh web
See scripts/README.md for scope, verdicts and specialist checks.
EOF
}

if [ "$#" -ne 1 ]; then usage >&2; exit 2; fi
case "$1" in
    -h|--help|help) usage; exit 0 ;;
    proof|web|all) ;;
    harness) exec python3 "$script_dir/test_web_harness.py" ;;
    *) usage >&2; exit 2 ;;
esac

# One path cannot identify both corpora, both cache formats or both outputs.
if [ "$1" = all ]; then
    for name in ALLOWLIST CACHE RESULTS_TSV DIFFDIR; do
        if [ -n "${!name:-}" ]; then
            echo "test.sh: $name requires a single suite (proof or web)" >&2
            exit 2
        fi
    done
fi

run_suite() (
    local suite=$1 engine default_list run_dir codes verdict
    case "$suite" in
        proof)
            engine=corpus_file_diff.sh
            default_list="$script_dir/parity_corpus.txt"
            export JOBS="${JOBS:-2}" HS_N="${HS_N:-4}"
            ;;
        web)
            engine=web_parity.sh
            default_list="$script_dir/websweep_residual.txt"
            export JOBS="${JOBS:-1}"
            ;;
    esac
    mkdir -p "${RESULTS_ROOT:-$script_dir/results}" || exit 2
    run_dir=$(mktemp -d "${RESULTS_ROOT:-$script_dir/results}/$suite.XXXXXXXX") || exit 2
    export ALLOWLIST="${ALLOWLIST:-$default_list}"
    export FILE_TIMEOUT="${FILE_TIMEOUT:-600}"
    export RESULTS_TSV="${RESULTS_TSV:-$run_dir/results.tsv}"
    export DIFFDIR="${DIFFDIR:-$run_dir/diffs}"
    export TAM_RS_NO_AUTO_BUILD=1
    echo "$suite: output directory $run_dir"
    echo "$suite: corpus $ALLOWLIST; results $RESULTS_TSV"
    bash "$script_dir/$engine" 2>&1 | tee "$run_dir/run.log"
    codes=("${PIPESTATUS[@]}")
    verdict=${codes[0]}
    # An unwritable/truncated log must not be presented as a successful run.
    if [ "$verdict" -eq 0 ] && [ "${codes[1]}" -ne 0 ]; then verdict=${codes[1]}; fi
    printf '%s\n' "$verdict" > "$run_dir/exit-code" || exit 2
    echo "$suite: exit $verdict; log $run_dir/run.log"
    exit "$verdict"
)

if [ "$1" = all ]; then
    proof_status=0
    web_status=0
    run_suite proof || proof_status=$?
    run_suite web || web_status=$?
    echo "Corpus exits: proof=$proof_status web=$web_status"
    [ "$proof_status" -eq 0 ] && [ "$web_status" -eq 0 ]
else
    run_suite "$1"
fi
