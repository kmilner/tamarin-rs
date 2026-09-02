#!/usr/bin/env python3
"""Focused regression tests for the pure web-gate harness helpers."""

import importlib.util
import os
import pathlib
import subprocess
import tempfile
import unittest


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("web_diff", HERE / "web_diff.py")
WEB_DIFF = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(WEB_DIFF)


class DiffArtifactNames(unittest.TestCase):
    def test_long_urls_with_the_same_prefix_do_not_collide(self):
        prefix = "/thy/trace/1/main/proof/" + "case/" * 50
        left = WEB_DIFF.safe_name(prefix + "left")
        right = WEB_DIFF.safe_name(prefix + "right")
        self.assertNotEqual(left, right)
        self.assertLessEqual(len(left), 168)

    def test_name_is_stable(self):
        url = "/thy/trace/1/main/message?proof=1"
        self.assertEqual(WEB_DIFF.safe_name(url), WEB_DIFF.safe_name(url))


class CacheProfiles(unittest.TestCase):
    def test_web_flags_exclude_batch_only_modes(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
printf 'auto.spthy\t--auto-sources\ndefine.spthy\t-D=A --stop-on-trace=seqdfs\n' \
    > "$t/flags.tsv"
WEB_FLAGS_MAP="$t/flags.tsv"
if web_flags_for auto.spthy 2>"$t/error"; then
    exit 1
fi
grep -F 'unsupported interactive flag for auto.spthy: --auto-sources' "$t/error"
test "$(web_flags_for define.spthy)" = '-D=A --stop-on-trace=seqdfs'
WEB_FLAGS_MAP="$t/missing.tsv"
if web_flags_for define.spthy 2>"$t/error"; then
    exit 1
fi
grep -F "map is not readable: $t/missing.tsv" "$t/error"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_manifest_follows_parser_preprocessing_and_heuristics(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus"
printf '%s\n' \
  'theory T begin' \
  '/* #include "commented-missing.spthy" */' \
  '#ifdef ACTIVE' \
  '#include "active-missing.spthy"' \
  '#else' \
  '#include /* gap */ "live.spthy"' \
  '#endif' \
  'lemma x [heuristic=o   "rank"]: "T"' \
  'end' \
  '#include "trailing-missing.spthy"' > "$t/corpus/t.spthy"
: > "$t/corpus/live.spthy"
printf '#!/bin/sh\n' > "$t/corpus/rank"

manifest=$(input_manifest "$t/corpus/t.spthy")
grep -F "$t/corpus/live.spthy" <<< "$manifest"
grep -F "$t/corpus/rank" <<< "$manifest"
! grep -F 'commented-missing' <<< "$manifest"
! grep -F 'trailing-missing' <<< "$manifest"
if input_manifest "$t/corpus/t.spthy" '-D=ACTIVE' 2>"$t/error"; then
    exit 1
fi
grep -F 'active-missing.spthy' "$t/error"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_deep_includes_are_fully_keyed_and_staged(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            (root / "root.spthy").write_text(
                'theory T begin\n#include "i1.spthy"\nend\n'
            )
            for i in range(1, 11):
                next_include = f'#include "i{i + 1}.spthy"\n' if i < 10 else ""
                (root / f"i{i}.spthy").write_text(next_include)
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
HS_FP_SALT=fingerprint
manifest=$(input_manifest "$t/root.spthy")
test "$(_include_shas_from_manifest "$manifest" | wc -l)" -eq 10
k1=$(ckey root.spthy "$t/root.spthy")
printf '%s\n' '/* changed */' > "$t/i10.spthy"
k2=$(ckey root.spthy "$t/root.spthy")
test "$k1" != "$k2"
mkdir "$t/staged"
web_stage_inputs "$t/root.spthy" "$t/staged"
test -f "$t/staged/i10.spthy"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_nonweb_cache_keys_include_oracle_scripts(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/proof_diff_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus"
printf '%s\n' 'theory T begin' 'heuristic: o' 'end' > "$t/corpus/t.spthy"
printf '%s\n' '#!/bin/sh' 'echo first' > "$t/corpus/t.oracle"
chmod +x "$t/corpus/t.oracle"
HS_FP_SALT=fingerprint

k1=$(ckey t.spthy "$t/corpus/t.spthy")
p1=$(proof_cache_key "$t/corpus/t.spthy" lemma)
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/corpus/t.oracle"
k2=$(ckey t.spthy "$t/corpus/t.spthy")
p2=$(proof_cache_key "$t/corpus/t.spthy" lemma)
test "$k1" != "$k2"
test "$p1" != "$p2"

printf '%s\n' 'theory Q begin' 'heuristic: o "rank.sh"' 'end' > "$t/corpus/q.spthy"
printf '%s\n' '#!/bin/sh' 'echo first' > "$t/corpus/rank.sh"
q1=$(ckey q.spthy "$t/corpus/q.spthy")
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/corpus/rank.sh"
q2=$(ckey q.spthy "$t/corpus/q.spthy")
test "$q1" != "$q2"

# Haskell's takeBaseName preserves a lone leading-dot component, so the
# default oracle for `.spthy` is `.spthy.oracle`, not `.oracle`.
printf '%s\n' 'theory Hidden begin' 'heuristic: o' 'end' > "$t/corpus/.spthy"
printf '%s\n' '#!/bin/sh' 'echo first' > "$t/corpus/.spthy.oracle"
h1=$(ckey .spthy "$t/corpus/.spthy")
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/corpus/.spthy.oracle"
h2=$(ckey .spthy "$t/corpus/.spthy")
test "$h1" != "$h2"

printf '%s\n' '#!/bin/sh' 'echo first' > "$t/custom-ranker"
c1=$(proof_cache_key "$t/corpus/q.spthy" lemma "--heuristic=o --oraclename=$t/custom-ranker")
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/custom-ranker"
c2=$(proof_cache_key "$t/corpus/q.spthy" lemma "--heuristic=o --oraclename=$t/custom-ranker")
test "$c1" != "$c2"

# CLI heuristics without --oraclename still resolve beside the theory and
# therefore need the same staged spelling when the web gate moves the input.
mkdir "$t/staged"
web_stage_inputs "$t/corpus/t.spthy" "$t/staged" '--heuristic=o'
test -f "$t/staged/t.oracle"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_included_oracles_are_keyed_and_staged_with_their_modes(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/proof_diff_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus/sub" "$t/staged"
printf '%s\n' 'theory T begin' '#include "sub/inc.spthy"' 'end' > "$t/corpus/t.spthy"
printf '%s\n' 'heuristic: o' 'lemma x [heuristic=o "rank"]: "T"' > "$t/corpus/sub/inc.spthy"
printf '%s\n' '#!/bin/sh' 'echo default-one' > "$t/corpus/sub/inc.oracle"
printf '%s\n' '#!/bin/sh' 'echo quoted-one' > "$t/corpus/sub/rank"
chmod +x "$t/corpus/sub/inc.oracle" "$t/corpus/sub/rank"
HS_FP_SALT=fingerprint

c1=$(ckey t.spthy "$t/corpus/t.spthy")
p1=$(proof_cache_key "$t/corpus/t.spthy" x)
w1=$(web_cache_key t.spthy "$t/corpus/t.spthy")
printf '%s\n' '#!/bin/sh' 'echo default-two' > "$t/corpus/sub/inc.oracle"
c2=$(ckey t.spthy "$t/corpus/t.spthy")
p2=$(proof_cache_key "$t/corpus/t.spthy" x)
w2=$(web_cache_key t.spthy "$t/corpus/t.spthy")
test "$c1" != "$c2" && test "$p1" != "$p2" && test "$w1" != "$w2"

web_stage_inputs "$t/corpus/t.spthy" "$t/staged"
test -f "$t/staged/sub/inc.spthy"
test -f "$t/staged/sub/inc.oracle"
test -f "$t/staged/sub/rank"
test ! -e "$t/staged/sub/oracle"
test "$(stat -c %a "$t/staged/sub/rank")" = \
     "$(stat -c %a "$t/corpus/sub/rank")"

printf '%s\n' '#!/bin/sh' 'echo linked' > "$t/target-oracle"
chmod 755 "$t/target-oracle"
rm -f "$t/corpus/sub/rank"
ln -s "$t/target-oracle" "$t/corpus/sub/rank"
m1=$(web_cache_key t.spthy "$t/corpus/t.spthy")
chmod 644 "$t/target-oracle"
m2=$(web_cache_key t.spthy "$t/corpus/t.spthy")
test "$m1" != "$m2"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_staging_preserves_each_lexical_include_alias(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus/a" "$t/corpus/b" "$t/staged"
printf '%s\n' 'theory T begin' '#include "a/inc.spthy"' \
    '#include "b/../a/inc.spthy"' 'end' > "$t/corpus/t.spthy"
: > "$t/corpus/a/inc.spthy"
web_stage_inputs "$t/corpus/t.spthy" "$t/staged"
test -d "$t/staged/b"
test -f "$t/staged/a/inc.spthy"
test -f "$t/staged/b/../a/inc.spthy"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_staging_rejects_relative_inputs_outside_destination(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus/nested/a" "$t/staged/s1/s2"
printf '%s\n' 'theory T begin' '#include "../../../outside.spthy"' 'end' \
    > "$t/corpus/nested/a/t.spthy"
: > "$t/outside.spthy"
if web_stage_inputs "$t/corpus/nested/a/t.spthy" "$t/staged/s1/s2" 2>"$t/error"; then
    exit 1
fi
grep -F 'staged path escapes destination: ../../../outside.spthy' "$t/error"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_staging_allows_dependencies_within_explicit_root(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus/macros" "$t/corpus/heuristic" "$t/staged/thy"
printf '%s\n' 'theory T begin' 'heuristic: o "../heuristic/rank"' 'end' \
    > "$t/corpus/macros/t.spthy"
printf '#!/bin/sh\n' > "$t/corpus/heuristic/rank"
chmod 755 "$t/corpus/heuristic/rank"
web_stage_inputs "$t/corpus/macros/t.spthy" "$t/staged/thy" '' "$t/staged"
test -x "$t/staged/heuristic/rank"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_missing_include_fails_manifest_keys_and_staging(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/proof_diff_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus" "$t/staged"
printf '%s\n' 'theory T begin' '#include "missing.spthy"' 'end' > "$t/corpus/t.spthy"
HS_FP_SALT=fingerprint
CACHE_VERSION=test

expect_failure() {
    if "$@" 2>"$t/error"; then
        echo "unexpected success: $*" >&2
        exit 1
    fi
    grep -F "failed to read included file $t/corpus/missing.spthy" "$t/error"
}
expect_failure ckey t.spthy "$t/corpus/t.spthy"
expect_failure proof_cache_key "$t/corpus/t.spthy" x
expect_failure web_cache_key t.spthy "$t/corpus/t.spthy"
expect_failure web_stage_inputs "$t/corpus/t.spthy" "$t/staged"
if file_sha256 "$t/corpus/absent.spthy" 2>"$t/error"; then
    exit 1
fi
grep -F "$t/corpus/absent.spthy" "$t/error"
if _include_shas_from_manifest \
        "$(printf 'S\t%s\tt.spthy\nS\t%s\tmissing.spthy\n' \
            "$t/corpus/t.spthy" "$t/corpus/absent.spthy")" 2>"$t/error"; then
    exit 1
fi
grep -F "$t/corpus/absent.spthy" "$t/error"
if input_manifest "$t/corpus/absent.spthy" 2>"$t/error"; then
    exit 1
fi
grep -F "$t/corpus/absent.spthy" "$t/error"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_profiles_keys_and_legacy_adoption(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            (root / "hs").write_bytes(b"oracle one")
            (root / "plain.spthy").write_text("theory Plain begin\nend\n")
            (root / "inc.spthy").write_text("/* one */\n")
            (root / "with-inc.spthy").write_text(
                'theory Included begin\n#include "inc.spthy"\nend\n'
            )
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
hs_fingerprint "$t/hs"
MAUDE_PATH="$t/hs"
old=$(sha256sum "$t/plain.spthy" | cut -d' ' -f1)
mkdir -p "$t/pool"
printf '%s\n' '{"__plan_version__":2,"manifest":{}}' > "$t/pool/$old.hs.json"
printf '%s\n' "$HS_FP" > "$t/pool/$old.hs.fp"
WEB_CACHE_ROOT="$t/pool"; unset CACHE
DERIVCHECK_TIMEOUT=30 MAX_NODES=400 web_cache_init "$PWD" "$PWD/scripts" "$t/hs" 2
first_cache=$CACHE
key=$(web_cache_key plain.spthy "$t/plain.spthy")
web_cache_adopt_legacy "$key" "$t/plain.spthy" 2
test "$(stat -c %i "$t/pool/$old.hs.json")" = "$(stat -c %i "$CACHE/$key.hs.json")"
test "$(cat "$CACHE/$key.hs.fp")" = "$WEB_ORACLE_SHA256"

k1=$(web_cache_key with-inc.spthy "$t/with-inc.spthy")
printf '/* two */\n' > "$t/inc.spthy"
k2=$(web_cache_key with-inc.spthy "$t/with-inc.spthy")
test "$k1" != "$k2"

printf 'oracle two\n' > "$t/hs"
hs_fingerprint "$t/hs"
unset CACHE
web_cache_init "$PWD" "$PWD/scripts" "$t/hs" 2
test "$first_cache" != "$CACHE"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

    def test_cache_publication_is_atomic_and_locked(self):
        with tempfile.TemporaryDirectory() as td:
            env = os.environ.copy()
            env["HARNESS_TMP"] = td
            subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/web_cache.sh
CACHE=$HARNESS_TMP/cache
WEB_CACHE_ORACLE_STAMP=oracle
mkdir -p "$CACHE"
printf '%s\n' '{"generation":0}' > "$HARNESS_TMP/a.json"
printf '%s\n' '{"generation":1}' > "$HARNESS_TMP/b.json"

# A second process cannot enter the same key while its lock is held.
web_cache_lock key
(
    # Do not retain the parent's lock descriptor in the contender.
    exec {WEB_CACHE_LOCK_FD}>&-
    : > "$HARNESS_TMP/attempted"
    web_cache_lock key
    : > "$HARNESS_TMP/acquired"
    web_cache_unlock
) & blocked_pid=$!
for _ in {1..100}; do
    [ ! -e "$HARNESS_TMP/attempted" ] || break
    sleep 0.01
done
test -e "$HARNESS_TMP/attempted"
test ! -e "$HARNESS_TMP/acquired"
web_cache_unlock
wait "$blocked_pid"
test -e "$HARNESS_TMP/acquired"

writer() {
    local i source
    for ((i=0; i<100; i++)); do
        source=$HARNESS_TMP/a.json
        ((i % 2)) && source=$HARNESS_TMP/b.json
        web_cache_lock key
        web_cache_publish key "$source"
        web_cache_unlock
    done
}

reader() {
    local i snapshot
    for ((i=0; i<100; i++)); do
        snapshot=$(mktemp "$HARNESS_TMP/read.XXXXXX")
        web_cache_lock key
        if [ -f "$CACHE/key.hs.fp" ]; then
            test "$(cat "$CACHE/key.hs.fp")" = "$WEB_CACHE_ORACLE_STAMP"
            cp "$CACHE/key.hs.json" "$snapshot"
        fi
        web_cache_unlock
        [ ! -s "$snapshot" ] || python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$snapshot"
        rm -f "$snapshot"
    done
}

writer & writer_pid=$!
reader & reader_pid=$!
wait "$writer_pid"
wait "$reader_pid"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )


if __name__ == "__main__":
    unittest.main()
