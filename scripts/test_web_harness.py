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


if __name__ == "__main__":
    unittest.main()
