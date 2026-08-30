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
    def test_deep_and_cyclic_includes_are_fully_keyed_and_staged(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            (root / "root.spthy").write_text('#include "i1.spthy"\n')
            for i in range(1, 11):
                next_include = f'#include "i{i + 1}.spthy"\n' if i < 10 else '#include "i1.spthy"\n'
                (root / f"i{i}.spthy").write_text(f"level {i}\n{next_include}")
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
test "$(include_shas "$t/root.spthy" | wc -l)" -eq 10
k1=$(ckey root.spthy "$t/root.spthy")
printf '%s\n' changed '#include "i1.spthy"' > "$t/i10.spthy"
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
t=$HARNESS_TMP
mkdir -p "$t/corpus"
printf '%s\n' 'theory T begin' 'heuristic: o' 'end' > "$t/corpus/t.spthy"
printf '%s\n' 't.spthy	@cd' > "$t/flags.tsv"
printf '%s\n' '#!/bin/sh' 'echo first' > "$t/corpus/t.oracle"
chmod +x "$t/corpus/t.oracle"
FLAGS_MAP="$t/flags.tsv"
HS_FP_SALT=fingerprint

k1=$(ckey t.spthy "$t/corpus/t.spthy")
p1=$(proof_cache_key "$t/corpus/t.spthy" lemma @cd)
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/corpus/t.oracle"
k2=$(ckey t.spthy "$t/corpus/t.spthy")
p2=$(proof_cache_key "$t/corpus/t.spthy" lemma @cd)
test "$k1" != "$k2"
test "$p1" != "$p2"

printf '%s\n' 'theory Q begin' 'heuristic: o "rank.sh"' 'end' > "$t/corpus/q.spthy"
printf '%s\n' '#!/bin/sh' 'echo first' > "$t/corpus/rank.sh"
q1=$(ckey q.spthy "$t/corpus/q.spthy")
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/corpus/rank.sh"
q2=$(ckey q.spthy "$t/corpus/q.spthy")
test "$q1" != "$q2"

printf '%s\n' '#!/bin/sh' 'echo first' > "$t/custom-ranker"
c1=$(proof_cache_key "$t/corpus/q.spthy" lemma "--oraclename=$t/custom-ranker")
printf '%s\n' '#!/bin/sh' 'echo second' > "$t/custom-ranker"
c2=$(proof_cache_key "$t/corpus/q.spthy" lemma "--oraclename=$t/custom-ranker")
test "$c1" != "$c2"
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
            (root / "inc.spthy").write_text("one\n")
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
printf 'two\n' > "$t/inc.spthy"
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
