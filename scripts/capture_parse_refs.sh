#!/usr/bin/env bash
# Capture the HASKELL oracle's `--parse-only` outcome for every row of
# crates/tamarin-parser/tests/fixtures/parse_cases.tsv, so
# crates/tamarin-parser/tests/parse_table.rs can check the port against it.
#
#   scripts/capture_parse_refs.sh
#
# Rewrites the `hs` column in place (`ok` on exit 0, `err` otherwise) and the
# `# oracle:` header line.  Only the outcome is recorded: Parsec's positions
# and messages are not a parity target.  Rows whose mode HS has no command
# line for (`intruder`) keep `-`.
#
# Env: HS_PATH (oracle binary; default: the pinned build, see
#      gate_common.sh resolve_hs_oracle), FILE_TIMEOUT (30s per row),
#      ALLOW_ORACLE_REV_MISMATCH=1 (capture against an oracle that is not the
#      submodule pin).
set -eu
[ "$#" -eq 0 ] || { echo "usage: scripts/capture_parse_refs.sh" >&2; exit 2; }

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
. "$script_dir/gate_common.sh"
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"

TABLE="$repo_root/crates/tamarin-parser/tests/fixtures/parse_cases.tsv"
[ -f "$TABLE" ] || { echo "capture_parse_refs: no table at $TABLE" >&2; exit 2; }

HS_PATH=$(resolve_hs_oracle "$repo_root") || exit 2
pin="$(git -C "$repo_root" rev-parse :tamarin-prover)"
binrev="$(timeout 60 "$HS_PATH" --version 2>/dev/null \
    | sed -n 's/^Git revision: \([0-9a-f]*\).*/\1/p')"
if [ "$binrev" != "$pin" ]; then
    echo "capture_parse_refs: oracle $HS_PATH is revision '${binrev:-unknown}' but the submodule pin is $pin" >&2
    [ "${ALLOW_ORACLE_REV_MISMATCH:-0}" = 1 ] || exit 2
fi

HS_PATH="$HS_PATH" ORACLE_REV="${binrev:-unknown}" FILE_TIMEOUT="${FILE_TIMEOUT:-30}" \
    python3 -I - "$TABLE" <<'PY'
import os, subprocess, sys, tempfile

table = sys.argv[1]
hs, rev, limit = os.environ["HS_PATH"], os.environ["ORACLE_REV"], int(os.environ["FILE_TIMEOUT"])

def unescape(cell):
    out, i = [], 0
    while i < len(cell):
        if cell[i] == "\\":
            out.append({"n": "\n", "t": "\t", "\\": "\\"}[cell[i + 1]])
            i += 2
        else:
            out.append(cell[i])
            i += 1
    return "".join(out)

def capture(mode, cell):
    words = mode.split()
    args = ["--parse-only"] + (["--diff"] if words[0] == "diff" else []) + words[1:]
    parts = unescape(cell).split("\n@@@ ")
    with tempfile.TemporaryDirectory(prefix="capture_parse_refs_") as d:
        for part in parts[1:]:
            path, _, body = part.partition("\n")
            path = os.path.join(d, path)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(body)
        root = os.path.join(d, "main.spthy")
        with open(root, "w", encoding="utf-8") as f:
            f.write(parts[0])
        rc = subprocess.run([hs, *args, root, "+RTS", "-N1", "-M2G", "-RTS"],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                            timeout=limit, cwd=d).returncode
    return "ok" if rc == 0 else "err"

lines = open(table, encoding="utf-8").read().split("\n")
counts = {"ok": 0, "err": 0}
for i, line in enumerate(lines):
    if line.startswith("# oracle:"):
        lines[i] = f"# oracle: {rev}"
    if not line or line.startswith("#"):
        continue
    cols = line.split("\t")
    if cols[1].split()[0] not in ("theory", "diff"):
        cols[2] = "-"
    else:
        cols[2] = capture(cols[1], cols[4])
        counts[cols[2]] += 1
    lines[i] = "\t".join(cols)
with tempfile.TemporaryDirectory(dir=os.path.dirname(table)) as tmp:
    updated = os.path.join(tmp, "parse_cases.tsv")
    with open(updated, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    os.replace(updated, table)
print(f"capture_parse_refs: {counts['ok']} ok, {counts['err']} err, oracle {rev}")
PY
