#!/usr/bin/env python3
"""Focused regression tests for parity-gate cache and certificate helpers."""

import html
import importlib.util
import json
import os
import pathlib
import socket
import subprocess
import tempfile
import unittest


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("web_diff", HERE / "web_diff.py")
WEB_DIFF = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(WEB_DIFF)
URL_SPEC = importlib.util.spec_from_file_location("web_url_key", HERE / "web_url_key.py")
WEB_URL_KEY = importlib.util.module_from_spec(URL_SPEC)
assert URL_SPEC.loader is not None
URL_SPEC.loader.exec_module(WEB_URL_KEY)

# Gate configuration is explicit test input, never ambient process state.
# Keep ordinary tool discovery (notably PATH), but prevent a developer's cache
# or corpus overrides from redirecting supposedly isolated scenarios.
GATE_ENV_KEYS = set("""
    ALLOWLIST ALLOW_ORACLE_REV_MISMATCH ALLOW_STALE_BIN
    BIN CACHE CORPUS CORPUS_ROOT DERIV
    DERIVCHECK_TIMEOUT DIFFDIR DOT_FP EXEC_FP EXEC_FP_SALT EXTRA_FLAGS
    FAIL_ON_CAPPED FAMILY FILE_TIMEOUT FLAGS_MAP HS_CACHE HS_FP HS_FP_SALT
    HS_PATH HS_PORT INPUT_MANIFEST_BIN JOBS MAUDE_PATH MAX_NODES OUT
    PORT_FREE_TIMEOUT READY_TIMEOUT REF RESULTS_TSV RETRY_TIMEOUT ROOT RS_BIN
    RS_FP RS_PATH RS_PORT SERVER_MEM_KB SERVER_STOP_TIMEOUT TAMARIN_RS_CACHE_ROOT
    TAM_RS_NO_AUTO_BUILD TIMEOUT WEB_CACHE_ROOT WEB_CRAWL_TIMEOUT WEB_FLAGS_MAP
    WEB_LEDGER WEB_ORACLE_SHA256 WEB_PRODUCER_PROTOCOL_FP WEB_TEST_PORT
    WEB_WORK_ROOT
""".split())


def clean_environment(overrides=None):
    env = os.environ.copy()
    for key in GATE_ENV_KEYS:
        env.pop(key, None)
    if overrides is not None:
        env.update(overrides)
    return env


def run_shell(script, *, temp_dir=None, env=None, check=True):
    """Run a harness scenario with an isolated scratch directory."""
    if temp_dir is None:
        with tempfile.TemporaryDirectory() as owned_temp:
            return run_shell(script, temp_dir=owned_temp, env=env, check=check)

    run_env = clean_environment(env)
    run_env["HARNESS_TMP"] = str(temp_dir)
    result = subprocess.run(
        ["bash", "-x", "-c", script],
        cwd=HERE.parent,
        env=run_env,
        capture_output=True,
        text=True,
    )
    if check and result.returncode:
        raise AssertionError(
            f"shell scenario exited {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


class ParserDiagnosticNormalization(unittest.TestCase):
    @staticmethod
    def normalize(stderr):
        return subprocess.run(
            ["bash", "-c", ". scripts/gate_common.sh; nerr"],
            cwd=HERE.parent,
            # Normalization must not preflight installed provers or Maude.
            env=clean_environment({
                "HS_PATH": "/nonexistent/haskell-oracle",
                "RS_BIN": "/nonexistent/tamarin-rs",
                "MAUDE_PATH": "/nonexistent/maude",
            }),
            input=stderr,
            text=True, capture_output=True, check=True,
        ).stdout

    def test_syntax_frames_agree(self):
        hs = '\"bad.spthy\" (line 2, column 1):\nunexpected \"?\"\nexpecting \"end\"\n'
        rs = "error[parse]: Unexpected input\n  ┌─ bad.spthy:2:1\n  │\n2 │ ?\n  │ ^\n  = expected end\n\n"
        self.assertEqual(self.normalize(hs), "<parser diagnostic>\n")
        self.assertEqual(self.normalize(rs), self.normalize(hs))

    def test_runtime_errors_remain_visible(self):
        for message in ["error: oracle failed\n", "tamarin-prover: runtime failure\n", "unknown diagnostic format\n"]:
            self.assertEqual(self.normalize(message), message)
            rs = "error[parse]: Bad syntax\n  │ ^\n\n"
            self.assertEqual(self.normalize(message + rs + message), message + "<parser diagnostic>\n" + message)
            self.assertEqual(self.normalize(rs.rstrip() + "\n" + message), "<parser diagnostic>\n" + message)

    def test_unrecognized_haskell_messages_are_not_suppressed(self):
        hs = '\"bad.spthy\" (line 2, column 1):\nunexpected \"?\"\nsemantic detail\nerror: oracle failed\n'
        self.assertEqual(self.normalize(hs), "<parser diagnostic>\nsemantic detail\nerror: oracle failed\n")

    def test_existing_warning_rules_still_apply(self):
        stderr = "[Open Chains] Too many chain constraints\n" * 2 + "[Saturating Sources] noise\nother warning\n"
        self.assertEqual(self.normalize(stderr), "[Open Chains] Too many chain constraints\nother warning\n")


class DiffArtifactNames(unittest.TestCase):
    def test_long_urls_with_the_same_prefix_do_not_collide(self):
        prefix = "/thy/trace/1/main/proof/" + "case/" * 50
        left = WEB_DIFF.safe_name(prefix + "left")
        right = WEB_DIFF.safe_name(prefix + "right")
        self.assertNotEqual(left, right)
        self.assertLessEqual(len(left), 168)

    def test_name_and_url_keys_are_stable(self):
        url = "/thy/trace/1/main/message?proof=1"
        self.assertEqual(
            WEB_DIFF.safe_name(url),
            "_thy_trace_1_main_message_proof=1__c21ac20dd08016f7",
        )
        self.assertEqual(
            WEB_URL_KEY.norm_url_key(url), "/thy/trace/#/main/message?proof=1"
        )
        self.assertEqual(
            WEB_URL_KEY.norm_url_key("/thy/equiv/42/overview"),
            "/thy/equiv/#/overview",
        )

    def test_comparison_normalizes_each_manifest_workdir(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            url = "/thy/trace/#/main/proof/example"
            hs_root = "/cache/web-work/run.HASKELL"
            rs_root = "/cache/web-work/run.RUST"
            common = {"kind": "text", "status": 200}
            for side, workdir in (("hs", hs_root), ("rs", rs_root)):
                doc = {
                    "workdir": workdir,
                    "manifest": {url: {
                        **common,
                        "body": f"oracle located at {workdir}/thy/oracle",
                    }},
                }
                (root / f"{side}.json").write_text(json.dumps(doc))
            subprocess.run(
                [
                    "python3",
                    str(HERE / "web_diff.py"),
                    str(root / "hs.json"),
                    str(root / "rs.json"),
                    str(root / "out.tsv"),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertEqual(
                (root / "out.tsv").read_text().split("\t")[1], "MATCH"
            )

    def test_workdir_normalization_handles_serialized_escaping(self):
        hs_root = '/cache/web&oracle"hs\'branch'
        rs_root = '/cache/web&oracle"rs\'branch'
        roots = (hs_root, rs_root)

        def escaped(root, apostrophe):
            return html.escape(root, quote=True).replace("&#x27;", apostrophe)

        for apostrophe in ("&#x27;", "&#39;", "&apos;"):
            hs = WEB_DIFF.canon(
                "html",
                f'<a href="{escaped(hs_root, apostrophe)}/x">'
                f"{escaped(hs_root, apostrophe)}</a>",
                roots,
            )
            rs = WEB_DIFF.canon(
                "html",
                f'<a href="{escaped(rs_root, apostrophe)}/x">'
                f"{escaped(rs_root, apostrophe)}</a>",
                roots,
            )
            self.assertEqual(hs, "<a href=/WEB-WORKDIR/x>\nT:/WEB-WORKDIR\n</a>")
            self.assertEqual(rs, hs)
            self.assertNotEqual(
                WEB_DIFF.canon(
                    "html",
                    f'<a href="{escaped(rs_root, apostrophe)}/x">changed</a>',
                    roots,
                ),
                hs,
            )

        hs_json_root = '/cache/web\\oracle"hs'
        rs_json_root = '/cache/web\\oracle"rs'
        json_roots = (hs_json_root, rs_json_root)
        hs = WEB_DIFF.canon(
            "json",
            json.dumps({"nested": [{"path": f"{hs_json_root}/x"}]}),
            json_roots,
        )
        rs = WEB_DIFF.canon(
            "json",
            json.dumps({"nested": [{"path": f"{rs_json_root}/x"}]}),
            json_roots,
        )
        self.assertEqual(
            hs,
            '{\n "nested": [\n  {\n   "path": "/WEB-WORKDIR/x"\n  }\n ]\n}',
        )
        self.assertEqual(rs, hs)
        self.assertNotEqual(
            WEB_DIFF.canon(
                "json",
                json.dumps({"nested": [{"path": f"{rs_json_root}/changed"}]}),
                json_roots,
            ),
            hs,
        )


class CacheProfiles(unittest.TestCase):
    def test_manifest_fields_round_trip_and_external_path_identity(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
original=$'dir/with\ttab/and\nnewline'
encoded=$(manifest_encode "$original")
manifest_decode_into "$encoded" decoded
test "$decoded" = "$original"
case "$encoded" in *$'\t'*|*$'\n'*) exit 1;; esac
if manifest_decode_into x:0 invalid; then exit 1; fi
if manifest_decode_into x:00 invalid; then exit 1; fi
# Adjacent zero nibbles across byte boundaries are not a NUL byte.
manifest_decode_into x:700a decoded
test "$decoded" = $'p\n'
if manifest_decode_into x:7000 invalid; then exit 1; fi

# Absolute includes have no staged alias, but their physical identity still
# distinguishes equal-content files in different locations.
t=$HARNESS_TMP
printf same > "$t/a"; printf same > "$t/b"
root=$(manifest_encode "$t/root")
a=$(manifest_encode "$t/a")
b=$(manifest_encode "$t/b")
empty=$(manifest_encode '')
ha=$(_include_shas_from_manifest "$(printf 'S\t%s\t%s\nS\t%s\t%s\n' "$root" "$root" "$a" "$empty")")
hb=$(_include_shas_from_manifest "$(printf 'S\t%s\t%s\nS\t%s\t%s\n' "$root" "$root" "$b" "$empty")")
test "$ha" != "$hb"
'''
        )

    def test_execution_identity_uses_versions_across_binary_builds(self):
        run_shell(r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
printf '%s\n' '#!/bin/sh' 'echo 3.5.1' > "$t/maude-a"
printf '%s\n' '#!/bin/sh' '# another platform build' 'echo 3.5.1' > "$t/maude-b"
chmod +x "$t/maude-a" "$t/maude-b"
execution_fingerprint "$t/maude-a" 30
first=$EXEC_FP
execution_fingerprint "$t/maude-b" 30
test "$first" = "$EXEC_FP"
execution_fingerprint "$t/maude-b" 31
test "$first" != "$EXEC_FP"
printf '%s\n' '#!/bin/sh' 'echo 3.6.0' > "$t/maude-b"
execution_fingerprint "$t/maude-b" 30
test "$first" != "$EXEC_FP"
printf '%s\n' '#!/bin/sh' 'exit 1' > "$t/maude-b"
if execution_fingerprint "$t/maude-b" 30; then exit 1; fi
''')

    def test_oracle_identity_tracks_revision_and_patches_across_rebuilds(self):
        run_shell(r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
for build in a b; do
    printf '%s\n' '#!/bin/sh' "# build $build" 'echo tamarin-prover 1.13.0' \
        'echo "Git revision: abc123, branch: main"' > "$t/hs-$build"
    chmod +x "$t/hs-$build"
    printf 'binary_sha256=%s\npatch_series_sha256=patch-a\n' \
        "$(binary_sha256 "$t/hs-$build")" > "$t/hs-$build.tamarin-rs-oracle"
done
hs_fingerprint "$t/hs-a"
first=$HS_FP
hs_fingerprint "$t/hs-b"
test "$first" = "$HS_FP"
sed -i 's/patch-a/patch-b/' "$t/hs-b.tamarin-rs-oracle"
hs_fingerprint "$t/hs-b"
test "$first" != "$HS_FP"
sed -i 's/abc123/def456/' "$t/hs-a"
printf 'binary_sha256=%s\npatch_series_sha256=patch-a\n' \
    "$(binary_sha256 "$t/hs-a")" > "$t/hs-a.tamarin-rs-oracle"
hs_fingerprint "$t/hs-a"
test "$first" != "$HS_FP"
''')

    def test_oracle_version_probe_uses_the_configured_maude(self):
        run_shell(r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
printf '%s\n' '#!/bin/sh' 'echo 3.5.1' > "$t/backend"
cat > "$t/hs" <<'SH'
#!/bin/sh
case "$1" in --with-maude=*) backend=${1#*=} ;; *) exit 1 ;; esac
"$backend" --version >/dev/null || exit 1
echo 'tamarin-prover 1.13.0'
SH
chmod +x "$t/backend" "$t/hs"
# The backend has no default executable name; only the explicit path works.
oracle_rev_check "$t/hs" "$t/backend" "$t"
MAUDE_PATH="$t/backend" WEB_WORK_ROOT="$t/work" WEB_CACHE_ROOT="$t/cache"
unset HS_FP
web_cache_init "$t" scripts "$t/hs" 2
''')

    def test_oracle_validation_reuses_one_probe_and_checks_the_attestation(self):
        run_shell(r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
export TEST_ORACLE_PIN=$(git rev-parse :tamarin-prover)
export TEST_ORACLE_CALLS="$t/calls"
printf '%s\n' '#!/bin/sh' 'echo 3.5.1' > "$t/backend"
cat > "$t/hs" <<'SH'
#!/bin/sh
case "$1" in --with-maude=*) ;; *) exit 1 ;; esac
echo called >> "$TEST_ORACLE_CALLS"
echo 'tamarin-prover 1.13.0'
echo "Git revision: $TEST_ORACLE_PIN (with uncommited changes), branch: HEAD"
SH
chmod +x "$t/hs" "$t/backend"
series=$(patch_series_fingerprint "$PWD")
printf 'binary_sha256=%s\npin=%s\npatch_series_sha256=%s\n' \
    "$(binary_sha256 "$t/hs")" "$TEST_ORACLE_PIN" "$series" > "$t/hs.tamarin-rs-oracle"
oracle_rev_check "$t/hs" "$t/backend" "$PWD"
test "$(wc -l < "$TEST_ORACLE_CALLS")" = 1
test "$ORACLE_SOURCE_STATUS" = verified
test "$ORACLE_REVISION" = "$TEST_ORACLE_PIN"
sed -i 's/^patch_series_sha256=.*/patch_series_sha256=wrong/' "$t/hs.tamarin-rs-oracle"
if (oracle_rev_check "$t/hs" "$t/backend" "$PWD") 2>"$t/error"; then exit 1; fi
grep -F 'different patch series' "$t/error"
printf '\n# replaced binary\n' >> "$t/hs"
if (oracle_rev_check "$t/hs" "$t/backend" "$PWD") 2>"$t/error"; then exit 1; fi
grep -F 'does not match any available setup.sh source attestation' "$t/error"
''')

    def test_producer_and_comparison_identities_detect_their_own_tools(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
printf '%s\n' '#!/bin/sh' 'echo hs-one' > "$t/hs"; printf '%s\n' '#!/bin/sh' 'echo 3.5.1' > "$t/maude"; printf rs > "$t/rs"
chmod +x "$t/hs" "$t/maude" "$t/rs"
hs_fingerprint "$t/hs"
execution_fingerprint "$t/maude" 30
rs_fingerprint "$t/rs"
producer_identity_unchanged
comparison_identity_unchanged
printf changed > "$t/rs"
producer_identity_unchanged
if comparison_identity_unchanged; then exit 1; fi
printf rs > "$t/rs"
rs_fingerprint "$t/rs"
printf changed > "$t/maude"
if producer_identity_unchanged; then exit 1; fi
'''
        )

    def test_web_profile_initialization_is_serialized(self):
        run_shell(
            r'''
set -e
t=$HARNESS_TMP
mkdir -p "$t/cache"
printf '%s\n' '#!/bin/sh' 'echo hs-one' > "$t/hs"; printf '%s\n' '#!/bin/sh' 'echo 3.5.1' > "$t/maude"
chmod +x "$t/hs" "$t/maude"
run_init() {
  CACHE="$t/cache" MAUDE_PATH="$t/maude" bash -c '
    . scripts/gate_common.sh
    . scripts/web_cache.sh
    web_cache_init "$HARNESS_TMP" scripts "$HARNESS_TMP/hs" "$1"
  ' _ "$1"
}
set +e
run_init one & a=$!
run_init two & b=$!
wait "$a"; ra=$?
wait "$b"; rb=$?
set -e
test $((ra == 0)) -ne $((rb == 0))
test -s "$t/cache/PROFILE"
'''
        )

    def test_web_shutdown_waits_for_the_complete_process_group(self):
        run_shell(
            r'''
set -e
. scripts/web_cache.sh
setsid bash -c 'trap "" TERM; sleep 30 & echo $! > "$1/child"' _ "$HARNESS_TMP" &
leader=$!
wait "$leader"
child=$(cat "$HARNESS_TMP/child")
kill -0 "$child"
SERVER_STOP_TIMEOUT=1 web_stop_group "$leader"
for _ in {1..20}; do
  state=$(ps -o stat= -p "$child" 2>/dev/null || true)
  case "$state" in ''|Z*) exit 0;; esac
  sleep .1
done
exit 1
'''
        )

    def test_shared_web_lifecycle_refuses_an_occupied_port(self):
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen()
            port = listener.getsockname()[1]
            run_shell(
                r'''
set -e
. scripts/web_cache.sh
if web_port_free "$WEB_TEST_PORT"; then exit 1; fi
declare -F web_boot_crawl >/dev/null
''',
                env={"WEB_TEST_PORT": str(port)},
            )

    def test_isolated_python_ignores_a_stale_local_bytecode_cache(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            module = root / "value.py"
            module.write_text("VALUE = 1\n")
            env = clean_environment()
            env["PYTHONPATH"] = td
            subprocess.run(["python3", "-c", "import value"], env=env, check=True)
            old_mtime = module.stat().st_mtime
            module.write_text("VALUE = 2\n")  # same size as the cached source
            os.utime(module, (old_mtime, old_mtime))
            run = run_shell(
                r'''
. scripts/web_cache.sh
web_python_isolated "$HARNESS_TMP/fresh-pycache" \
    python3 -c 'import value; print(value.VALUE)'
''',
                temp_dir=td,
                env=env,
            )
            self.assertEqual(run.stdout.strip(), "2")

    def test_crawl_lemma_metadata_is_required_and_uses_load_flags(self):
        run_shell(
            r'''
set -e
. scripts/web_cache.sh
parser_input_manifest() {
    test "$1" = theory.spthy
    test "$2" = '-D=ACTIVE'
    printf 'M\thas_lemmas\t%s\n' "$present"
}
present=0
test "$(web_crawl_args_for_theory theory.spthy '-D=ACTIVE')" = --allow-no-lemmas
present=1
test -z "$(web_crawl_args_for_theory theory.spthy '-D=ACTIVE')"
present=invalid
if web_crawl_args_for_theory theory.spthy '-D=ACTIVE'; then exit 1; fi
parser_input_manifest() { return 1; }
if web_crawl_args_for_theory theory.spthy; then exit 1; fi
parser_input_manifest() { printf 'S\troot\troot\n'; }
if web_crawl_args_for_theory theory.spthy; then exit 1; fi
'''
        )

    def test_diagnostics_publish_only_from_staging(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/staged" "$t/root"
ln -s "$t/root" "$t/root-link"
target=$(web_diagnostic_target "$t/root" '../../escape/file.spthy')
for alias in "$t/root/" "$t/root/./" "$t/root/sub/.." "$t/root-link"; do
    test "$target" = "$(web_diagnostic_target "$alias" '../../escape/file.spthy')"
done
test "$target" = "$(cd "$t" && web_diagnostic_target root '../../escape/file.spthy')"
case "$target" in "$t/root"/*) ;; *) exit 1;; esac
case "$target" in *'/../'*) exit 1;; esac
printf diagnostic > "$t/staged/page.diff"
test ! -e "$target/page.diff"

# Equivalent parent spellings must contend on the same lock.
lock_id=$(printf '%s' "$target" | sha256sum | cut -c1-16)
exec {held_fd}>"$t/root/.web-diagnostics.$lock_id.lock"
flock "$held_fd"
flock() {
    if [ "${1:-}" != -u ]; then
        readlink "/proc/$BASHPID/fd/$1" > "$t/flock-path"
        : > "$t/flock-entered"
    fi
    command flock "$@"
}
(
    exec {held_fd}>&-
    web_publish_diagnostics "$t/staged" "$t/root-link/../root/$(basename "$target")"
    : > "$t/finished"
) & publisher=$!
for _ in {1..100}; do
    [ ! -e "$t/flock-entered" ] || break
    sleep .01
done
test -e "$t/flock-entered"
test "$(cat "$t/flock-path")" = "$t/root/.web-diagnostics.$lock_id.lock"
test ! -e "$t/finished"
flock -u "$held_fd"; exec {held_fd}>&-
wait "$publisher"
test -e "$t/finished"
test "$(cat "$target/page.diff")" = diagnostic
test -d "$target" && test ! -L "$target"

# A failed staging copy leaves the previously published tree untouched.
rm "$t/staged/page.diff"
printf replacement > "$t/staged/other.diff"
cp() { return 1; }
if web_publish_diagnostics "$t/staged" "$target"; then exit 1; fi
test "$(cat "$target/page.diff")" = diagnostic
test ! -e "$target/other.diff"
unset -f cp
web_publish_diagnostics "$t/staged" "$target"
test ! -e "$target/page.diff"
test "$(cat "$target/other.diff")" = replacement

rm "$t/staged/other.diff"
web_publish_diagnostics "$t/staged" "$target"
test ! -e "$target"
'''
        )

    def test_conservative_manifest_catches_parser_omissions(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
mkdir -p "$t/sub"
printf '#include "sub/hidden.spthy"\n' > "$t/root.spthy"
printf 'first\n' > "$t/sub/hidden.spthy"
parser_input_manifest() { printf 'S\t%s\troot.spthy\n' "$1"; }
k1=$(input_content_key "$t/root.spthy")
printf 'second\n' > "$t/sub/hidden.spthy"
k2=$(input_content_key "$t/root.spthy")
test "$k1" != "$k2"
printf '#!/bin/sh\nfirst\n' > "$t/oracle-hidden"
k3=$(input_content_key "$t/root.spthy")
printf '#!/bin/sh\nsecond\n' > "$t/oracle-hidden"
k4=$(input_content_key "$t/root.spthy")
test "$k3" != "$k4"

# Syntax-invalid parity fixtures still get a conservative, content-sensitive
# identity instead of becoming permanently uncacheable.
parser_input_manifest() { echo 'syntax error' >&2; return 1; }
k5=$(input_content_key "$t/root.spthy")
printf 'third\n' > "$t/sub/hidden.spthy"
k6=$(input_content_key "$t/root.spthy")
test "$k5" != "$k6"
'''
        )

    def test_cache_root_is_shared_and_migrates_main_legacy_directory(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
git init -q "$t/repo"
mkdir -p "$t/repo/scripts/.old"
printf preserved > "$t/repo/scripts/.old/entry"
resolved=$(shared_cache_dir "$t/repo" proof "$t/repo/scripts/.old")
test "$resolved" = "$t/repo/scripts/.gate_cache/proof"
test -f "$resolved/entry"
test ! -e "$t/repo/scripts/.old"
'''
        )

    def test_nonweb_proof_cache_publication_and_validation(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/proof_diff_common.sh
t=$HARNESS_TMP
printf payload > "$t/source"
cache_entry_lock "$t" key fd
cache_publish_proof "$t/key.rc" "$t/key.full.gz" 0 "$t/source"
cache_gzip_valid "$t/key.full.gz"
proof_cache_result "$t/key.rc" "$t/key.full.gz" status
test "$status" = 0
test "$(gzip -dc "$t/key.full.gz")" = payload
cache_entry_unlock "$fd"
printf invalid > "$t/key.rc"
if proof_cache_result "$t/key.rc" "$t/key.full.gz" status; then exit 1; fi
printf 124 > "$t/key.rc"
if proof_cache_result "$t/key.rc" "$t/key.full.gz" status; then exit 1; fi
rm -f "$t/key.rc" "$t/key.full.gz"
# The payload helper must stop if the status sidecar cannot be published.
cache_publish_text() { return 1; }
if cache_publish_proof "$t/key.rc" "$t/key.full.gz" 0 "$t/source"; then exit 1; fi
test ! -e "$t/key.full.gz"
printf broken > "$t/broken.gz"
if cache_gzip_valid "$t/broken.gz"; then exit 1; fi
'''
        )

    def test_silent_nonzero_run_is_transient(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
: > "$t/out"
: > "$t/err"
transient_silent_failure 1 "$t/out" "$t/err"
! transient_silent_failure 0 "$t/out" "$t/err"
printf diagnostic > "$t/err"
! transient_silent_failure 1 "$t/out" "$t/err"
'''
        )

    def test_shared_gate_output_has_one_writer(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
claim_output "$t/result.tsv" owner_fd
printf 'owner\n' > "$t/result.tsv"
(
    exec {owner_fd}>&-
    ! claim_output "$t/result.tsv" contender_fd
)
test "$(cat "$t/result.tsv")" = owner
exec {owner_fd}>&-
claim_output "$t/result.tsv" next_fd
test ! -s "$t/result.tsv"
'''
        )

    def test_missing_dep_info_input_marks_release_binary_stale(self):
        run = run_shell(
            r'''
. scripts/gate_common.sh
t=$HARNESS_TMP
mkdir -p "$t/repo/crates"
# An external/sealed executable's dep-info belongs to another source tree and
# is intentionally not interpreted against this checkout.
printf '#!/bin/sh\nexit 0\n' > "$t/external"
chmod +x "$t/external"
printf '%s: missing.rs\n' "$t/external" > "$t/external.d"
rs_stale_check "$t/external" "$t/repo"
test -n "$RS_FP"

# An in-tree Cargo target retains the strict source/dep-info freshness check.
mkdir -p "$t/repo/target/release"
bin="$t/repo/target/release/tamarin-rs"
printf '#!/bin/sh\nexit 0\n' > "$bin"
chmod +x "$bin"
printf '%s: missing.rs\n' "$bin" > "$bin.d"
rs_stale_check "$bin" "$t/repo"
''',
            check=False,
        )
        self.assertEqual(run.returncode, 2)
        self.assertIn("dep-info names missing source", run.stderr)

    def test_reference_generation_rejects_uncertified_proof_bytes(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            corpus = root / "corpus"
            corpus.mkdir()
            theory = corpus / "t.spthy"
            theory.write_text("theory T begin\nend\n")
            (root / "allow").write_text("t.spthy\n")
            fake_bin = root / "fake-rs"
            fake_bin.write_text(
                "#!/usr/bin/env bash\n"
                "for arg in \"$@\"; do\n"
                "  if [ \"$arg\" = input-manifest ]; then\n"
                "    theory=${!#}; printf 'S\\t%s\\tt.spthy\\n' \"$theory\"; exit\n"
                "  fi\n"
                "done\n"
                "printf 'certified output\\n'\n"
            )
            fake_hs = root / "fake-hs"
            fake_hs.write_text("#!/bin/sh\necho 'Git revision: fake'\n")
            fake_maude = root / "maude"
            fake_maude.write_text("#!/bin/sh\necho fake-maude\n")
            for path in (fake_bin, fake_hs, fake_maude):
                path.chmod(0o755)
            env = clean_environment()
            env.update(
                BIN=str(fake_bin),
                MAUDE_PATH=str(fake_maude),
                CORPUS=str(corpus),
                ALLOWLIST=str(root / "allow"),
                FLAGS_MAP=str(root / "no-flags"),
                REF=str(root / "ref"),
                HS_PATH=str(fake_hs),
                ALLOW_ORACLE_REV_MISMATCH="1",
                EXTRA_FLAGS="",
            )
            identities = subprocess.run(
                [
                    "bash",
                    "-c",
                    r'''
set -e
. scripts/gate_common.sh
hs_fingerprint "$HS_PATH"
execution_fingerprint "$MAUDE_PATH" 30
scope=$(input_scope_fingerprint "$CORPUS" "$FLAGS_MAP" t.spthy)
key=$(input_content_key "$CORPUS/t.spthy")
out=$(printf 'certified output\n' | sha256sum | cut -d' ' -f1)
proof=$(printf 't.spthy\t%s\t%s\n' "$key" "$out" | sha256sum | cut -d' ' -f1)
printf '%s\n%s\n%s\n%s\n' "$scope" "$proof" "$HS_FP" "$EXEC_FP"
''',
                ],
                cwd=HERE.parent,
                env=env,
                check=True,
                capture_output=True,
                text=True,
            ).stdout.splitlines()
            scope, proof, oracle, execution = identities
            cert = root / "cert.log"
            cert.write_text(
                "DONE_CORPUS_FILE_DIFF verdict=OK files=1 "
                f"scope_sha256={scope} proof_outputs_sha256={'0' * 64} "
                f"oracle_sha256={oracle} execution_sha256={execution}\n"
            )
            run = subprocess.run(
                [
                    "bash",
                    "scripts/rs_ref_check.sh",
                    "generate",
                    "--certified-by",
                    str(cert),
                ],
                cwd=HERE.parent,
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(run.returncode, 1, run.stdout + run.stderr)
            self.assertIn("outputs differ from the certifying", run.stderr)
            self.assertFalse((root / "ref").exists())
            cert.write_text(
                "DONE_CORPUS_FILE_DIFF verdict=OK files=1 "
                f"scope_sha256={scope} proof_outputs_sha256={proof} "
                f"oracle_sha256={oracle} execution_sha256={execution}\n"
            )
            accepted = subprocess.run(
                [
                    "bash",
                    "scripts/rs_ref_check.sh",
                    "generate",
                    "--certified-by",
                    str(cert),
                ],
                cwd=HERE.parent,
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
            self.assertIn(
                f"# certified-proof-outputs-sha256: {proof}",
                (root / "ref").read_text(),
            )

    def test_scope_certificate_includes_per_file_flags(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus"
printf 'theory T begin\nend\n' > "$t/corpus/t.spthy"
input_manifest() { printf 'S\t%s\tt.spthy\n' "$1"; }
printf 't.spthy\t-D=A\n' > "$t/flags.tsv"
key=$(input_content_key "$t/corpus/t.spthy" '-D=A')
test "${#key}" -eq 64
first=$(input_scope_fingerprint "$t/corpus" "$t/flags.tsv" t.spthy)
printf 't.spthy\t-D=B\n' > "$t/flags.tsv"
second=$(input_scope_fingerprint "$t/corpus" "$t/flags.tsv" t.spthy)
test "$first" != "$second"
'''
        )

    def test_rs_reference_requires_full_certificate_before_proofs(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            corpus = root / "corpus"
            corpus.mkdir()
            (corpus / "t.spthy").write_text("theory T begin\nend\n")
            (root / "allow").write_text("t.spthy\n")
            (root / "ref").write_text(
                "# maude: fake-maude\n"
                "# oracle: 123.456\n"
                "t.spthy\tstale\tdeadbeef\t1\n"
            )
            fake_bin = root / "fake-rs"
            fake_bin.write_text(
                "#!/bin/sh\n"
                "if [ \"$1\" = input-manifest ]; then\n"
                "  printf 'S\\t%s\\tt.spthy\\n' \"$2\"\n"
                "else\n"
                f"  touch {root / 'proved'}\n"
                "fi\n"
            )
            fake_maude = root / "maude"
            fake_maude.write_text("#!/bin/sh\necho fake-maude\n")
            fake_bin.chmod(0o755)
            fake_maude.chmod(0o755)
            env = clean_environment()
            env.update(
                BIN=str(fake_bin),
                MAUDE_PATH=str(fake_maude),
                CORPUS=str(corpus),
                ALLOWLIST=str(root / "allow"),
                FLAGS_MAP=str(root / "no-flags"),
                REF=str(root / "ref"),
            )
            run = subprocess.run(
                ["bash", "scripts/rs_ref_check.sh", "check"],
                cwd=HERE.parent,
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
            self.assertIn("valid 64-hex oracle certificate", run.stderr)
            self.assertFalse((root / "proved").exists())

    def test_web_flags_exclude_batch_only_modes(self):
        run_shell(
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
'''
        )

    def test_manifest_follows_parser_preprocessing_and_heuristics(self):
        run_shell(
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
  '#include "diff-item.spthy"' \
  '#include "acc-item.spthy"' \
  'lemma x [heuristic=o   "rank"]: "T"' \
  'end' \
  '#include "trailing-missing.spthy"' > "$t/corpus/t.spthy"
: > "$t/corpus/live.spthy"
printf '%s\n' 'diffLemma observational [heuristic=o "diff-rank"]:' \
    > "$t/corpus/diff-item.spthy"
printf '%s\n' \
  'test blamed: "T"' \
  'lemma acc [heuristic=o "acc-rank"]:' \
  '  blamed accounts for "T"' > "$t/corpus/acc-item.spthy"
for rank in rank diff-rank acc-rank; do
    printf '#!/bin/sh\n' > "$t/corpus/$rank"
done

# This scenario targets parser provenance rather than the conservative fallback.
parser_input_manifest "$t/corpus/t.spthy" '--diff' > "$t/exact.tsv"
manifest=$(input_manifest "$t/corpus/t.spthy" '--diff')
sources= oracles= staged_oracles=
while IFS=$'\t' read -r tag source_field staged_field; do
    manifest_decode_into "$source_field" source
    manifest_decode_into "$staged_field" staged
    case "$tag" in
      S) sources+="$source"$'\n' ;;
      O) oracles+="$source"$'\n'; staged_oracles+="$staged"$'\n' ;;
    esac
done <<< "$manifest"
for include in live.spthy diff-item.spthy acc-item.spthy; do
    grep -F "$t/corpus/$include" <<< "$sources"
done
for rank in rank diff-rank acc-rank; do
    grep -F "$t/corpus/$rank" <<< "$oracles"
    grep -F "$rank" <<< "$staged_oracles"
done
! grep -F 'commented-missing' <<< "$sources"
! grep -F 'trailing-missing' <<< "$sources"
if input_manifest "$t/corpus/t.spthy" '-D=ACTIVE --diff' 2>"$t/error"; then
    exit 1
fi
grep -F 'active-missing.spthy' "$t/error"
'''
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
            run_shell(
                r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
HS_FP_SALT=fingerprint
EXEC_FP_SALT=execution
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
                temp_dir=td,
            )

    def test_nonweb_cache_keys_include_oracle_scripts(self):
        run_shell(
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
EXEC_FP_SALT=execution

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
'''
        )

    def test_included_oracles_are_keyed_and_staged_with_their_modes(self):
        run_shell(
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
EXEC_FP_SALT=execution

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
'''
        )

    def test_staging_preserves_trailing_newlines_in_paths(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
name=$'t.spthy\n'
dir=$'sub\n'
mkdir -p "$t/corpus/$dir" "$t/staged"
printf '%s\n' 'theory Wrong begin end' > "$t/corpus/t.spthy"
printf 'theory Right begin\n#include "%s/inc.spthy"\nend\n' "$dir" > "$t/corpus/$name"
printf '%s\n' 'rule R: [] --> []' > "$t/corpus/$dir/inc.spthy"
web_stage_inputs "$t/corpus/$name" "$t/staged"
cmp "$t/corpus/$name" "$t/staged/$name"
cmp "$t/corpus/$dir/inc.spthy" "$t/staged/$dir/inc.spthy"
test ! -e "$t/staged/t.spthy"
first=$(input_content_key "$t/corpus/$name")
printf '%s\n' 'theory Changed begin end' > "$t/corpus/t.spthy"
test "$first" = "$(input_content_key "$t/corpus/$name")"
printf '\nrule S: [] --> []\n' >> "$t/corpus/$dir/inc.spthy"
test "$first" != "$(input_content_key "$t/corpus/$name")"
'''
        )

    def test_staging_preserves_each_lexical_include_alias(self):
        run_shell(
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
'''
        )

    def test_staging_preserves_symlink_include_resolution(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus" "$t/real" "$t/staged"
printf '%s\n' 'theory T begin' '#include "alias.inc"' 'end' > "$t/corpus/t.spthy"
printf '%s\n' '#include "nested.inc"' > "$t/real/fragment.inc"
ln -s ../real/fragment.inc "$t/corpus/alias.inc"
printf '%s\n' 'lemma correct: "T" by sorry' > "$t/corpus/nested.inc"
printf '%s\n' 'lemma wrong: "T" by sorry' > "$t/real/nested.inc"
web_stage_inputs "$t/corpus/t.spthy" "$t/staged"
cmp "$t/corpus/nested.inc" "$t/staged/nested.inc"

# The independent scanner must also follow the lexical include directory.
# Simulate the parser omitting that dependency and verify invalidation.
parser_input_manifest() { printf 'S\t%s\tt.spthy\n' "$1"; }
k1=$(input_content_key "$t/corpus/t.spthy")
printf '%s\n' 'lemma changed: "T" by sorry' > "$t/corpus/nested.inc"
k2=$(input_content_key "$t/corpus/t.spthy")
test "$k1" != "$k2"
'''
        )

    def test_staging_excludes_conservative_only_dependencies(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus" "$t/staged"
printf '%s\n' 'theory T begin' '/* #include "unrelated.spthy" */' \
    '#ifdef UNUSED' '#include "inactive.spthy"' '#endif' 'end' > "$t/corpus/t.spthy"
printf '%s\n' 'theory Unrelated begin end' > "$t/corpus/unrelated.spthy"
printf '%s\n' 'theory Inactive begin end' > "$t/corpus/inactive.spthy"
web_stage_inputs "$t/corpus/t.spthy" "$t/staged"
test -f "$t/staged/t.spthy"
test ! -e "$t/staged/unrelated.spthy"
test ! -e "$t/staged/inactive.spthy"
k1=$(input_content_key "$t/corpus/t.spthy")
printf '%s\n' 'theory Changed begin end' > "$t/corpus/inactive.spthy"
k2=$(input_content_key "$t/corpus/t.spthy")
test "$k1" != "$k2"
'''
        )

    def test_staging_rejects_conflicting_destinations_before_copying(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/staged"
printf original > "$t/staged/shared.inc"
printf first > "$t/first.inc"
printf second > "$t/second.inc"
parser_input_manifest() {
    printf 'S\t%s\tshared.inc\nS\t%s\tsub/../shared.inc\n' "$t/first.inc" "$t/second.inc"
}
if web_stage_inputs "$t/first.inc" "$t/staged" 2>"$t/error"; then exit 1; fi
grep -F 'conflicting inputs for staged path' "$t/error"
test "$(cat "$t/staged/shared.inc")" = original
test ! -e "$t/staged/sub"
'''
        )

    def test_staging_rejects_relative_inputs_outside_destination(self):
        run_shell(
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
'''
        )

    def test_staging_allows_dependencies_within_explicit_root(self):
        run_shell(
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
'''
        )

    def test_missing_include_fails_manifest_keys_and_staging(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/proof_diff_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
mkdir -p "$t/corpus" "$t/staged"
printf '%s\n' 'theory T begin' '#include "missing.spthy"' 'end' > "$t/corpus/t.spthy"
HS_FP_SALT=fingerprint
EXEC_FP_SALT=execution
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
'''
        )

    def test_profiles_cover_execution_and_do_not_adopt_unproven_legacy(self):
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td)
            (root / "hs").write_text("#!/bin/sh\necho oracle-one\n")
            (root / "plain.spthy").write_text("theory Plain begin\nend\n")
            (root / "inc.spthy").write_text("/* one */\n")
            (root / "with-inc.spthy").write_text(
                'theory Included begin\n#include "inc.spthy"\nend\n'
            )
            (root / "dot").write_text("#!/bin/sh\necho dot-one\n")
            scripts = root / "scripts"
            scripts.mkdir()
            for name in (
                "web_crawl.py",
                "web_url_key.py",
                "web_diff.py",
                "web_normalize.py",
            ):
                (scripts / name).write_bytes((HERE / name).read_bytes())
            (root / "hs").chmod(0o755)
            (root / "dot").chmod(0o755)
            run_shell(
                r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
t=$HARNESS_TMP
hs_fingerprint "$t/hs"
MAUDE_PATH="$t/hs"
PATH="$t:$PATH"
old=$(sha256sum "$t/plain.spthy" | cut -d' ' -f1)
mkdir -p "$t/pool"
printf '%s\n' '{"__plan_version__":2,"manifest":{}}' > "$t/pool/$old.hs.json"
printf '%s\n' "$HS_FP" > "$t/pool/$old.hs.fp"
WEB_CACHE_ROOT="$t/pool"; unset CACHE
DERIVCHECK_TIMEOUT=30 MAX_NODES=400 web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
web_comparator_init "$t/scripts"
first_cache=$CACHE
# Rebuilding either executable without a version change keeps the profile.
printf '\n# another build\n' >> "$t/hs"
printf '\n# another build\n' >> "$t/dot"
hs_fingerprint "$t/hs"
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$first_cache" = "$CACHE"
test "$(web_crawl_constant "$t/scripts/web_crawl.py" PLAN_VERSION)" = 2
test "$(web_crawl_constant "$t/scripts/web_crawl.py" PLAN_VERSION_KEY)" = __plan_version__
key=$(web_cache_key plain.spthy "$t/plain.spthy")
test ! -e "$CACHE/$key.hs.json"

mkdir -p "$t/legacy"
printf '%s\n' '{"manifest":{}}' > "$t/legacy/old.hs.json"
CACHE="$t/legacy"
if web_cache_init "$PWD" "$t/scripts" "$t/hs" 2 2>"$t/legacy-error"; then
    exit 1
fi
grep -F 'has no complete producer profile' "$t/legacy-error"
test ! -e "$CACHE/PROFILE"
test "$(cat "$CACHE/old.hs.json")" = '{"manifest":{}}'

CACHE="$first_cache"
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$CACHE" = "$first_cache"

# Request deadlines do not affect a successful manifest and therefore do not
# fork the cache. Graphviz versions and derivation limits do.
unset CACHE; WEB_CRAWL_TIMEOUT=1
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$first_cache" = "$CACHE"
unset CACHE; DERIVCHECK_TIMEOUT=31
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$first_cache" != "$CACHE"
DERIVCHECK_TIMEOUT=30
printf '%s\n' '#!/bin/sh' 'echo dot-two' > "$t/dot"; chmod +x "$t/dot"
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$first_cache" != "$CACHE"

k1=$(web_cache_key with-inc.spthy "$t/with-inc.spthy")
printf '/* two */\n' > "$t/inc.spthy"
k2=$(web_cache_key with-inc.spthy "$t/with-inc.spthy")
test "$k1" != "$k2"

printf '%s\n' '#!/bin/sh' 'echo oracle-two' > "$t/hs"; chmod +x "$t/hs"
hs_fingerprint "$t/hs"
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$first_cache" != "$CACHE"

# Crawler implementation bytes are producer identity, independently of the
# manually maintained route-plan version.
crawler_cache=$CACHE
printf '\n# changed crawler\n' >> "$t/scripts/web_crawl.py"
if web_harness_identity_unchanged; then exit 1; fi
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$crawler_cache" != "$CACHE"

url_key_cache=$CACHE
printf '\n# changed URL key\n' >> "$t/scripts/web_url_key.py"
if web_harness_identity_unchanged; then exit 1; fi
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$url_key_cache" != "$CACHE"

# Shell staging and invocation behavior is producer identity too. Hashing the
# loaded protocol avoids coupling the profile to comparator/cache-only edits.
protocol_cache=$CACHE
web_crawl_args_for_theory() { printf '%s\n' --changed-producer-protocol; }
if web_harness_identity_unchanged; then exit 1; fi
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$protocol_cache" != "$CACHE"

# Lifecycle-only changes do not alter completed manifests and therefore keep
# the expensive producer profile reusable.
workdir_cache=$CACHE
web_make_workdir() { return 1; }
web_stop_group() { return 1; }
web_harness_identity_unchanged
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
test "$workdir_cache" = "$CACHE"

# Comparison-only changes invalidate the in-flight verdict identity, but do not
# strand reusable Haskell manifests in another producer profile.
comparator_cache=$CACHE
printf '\n# changed normalizer\n' >> "$t/scripts/web_normalize.py"
web_harness_identity_unchanged
if web_comparator_identity_unchanged; then exit 1; fi
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
web_comparator_init "$t/scripts"
test "$comparator_cache" = "$CACHE"
printf '\n# changed differ\n' >> "$t/scripts/web_diff.py"
web_harness_identity_unchanged
if web_comparator_identity_unchanged; then exit 1; fi
unset CACHE
web_cache_init "$PWD" "$t/scripts" "$t/hs" 2
web_comparator_init "$t/scripts"
test "$comparator_cache" = "$CACHE"
''',
                temp_dir=td,
            )

    def test_blank_haskell_load_is_not_cached(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
HS_CACHE=$HARNESS_TMP/cache
HS_PATH=$HARNESS_TMP/hs
MAUDE=maude
DERIVCHECK_TIMEOUT=5
mkdir -p "$HS_CACHE"
printf '#!/usr/bin/env bash\nprintf "\\n"\n' > "$HS_PATH"
chmod +x "$HS_PATH"
: > "$HARNESS_TMP/input.spthy"
ckey() { printf '%s\n' key; }
producer_identity_unchanged() { return 0; }
hs_load_cache_fill input "$HARNESS_TMP/input.spthy" key '' 5
test ! -e "$HS_CACHE/key.load.gz"

# Complete-looking output from a failed oracle process is not a reference.
printf '#!/usr/bin/env bash\nprintf "payload\\n"\nexit 1\n' > "$HS_PATH"
hs_load_cache_fill input "$HARNESS_TMP/input.spthy" key '' 5
test ! -e "$HS_CACHE/key.load.gz"

# A normalizer failure must not publish its partial output either.
printf '#!/usr/bin/env bash\nprintf "payload\\n"\n' > "$HS_PATH"
strip_env() { printf 'partial\n'; return 1; }
hs_load_cache_fill input "$HARNESS_TMP/input.spthy" key '' 5
test ! -e "$HS_CACHE/key.load.gz"
'''
        )

    def test_manifest_plan_probe_reads_only_declared_prefix(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
. scripts/web_cache.sh
printf '%s\n' '{"base":"x","__plan_version__":2,"manifest":{"body":"__plan_version__: 9"}}' > "$HARNESS_TMP/manifest.json"
test "$(web_manifest_plan_version "$HARNESS_TMP/manifest.json" __plan_version__)" = 2
printf '%s\n' '{"base":"x","manifest":{},"__plan_version__":2}' > "$HARNESS_TMP/late.json"
if web_manifest_plan_version "$HARNESS_TMP/late.json" __plan_version__; then exit 1; fi
'''
        )

    def test_cache_publication_is_atomic_and_locked(self):
        run_shell(
            r'''
set -e
. scripts/gate_common.sh
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

# A new writer prunes only a prior stage with the exact key-derived prefix and
# six-character mktemp suffix.
stage_id=$(printf '%s' key | sha256sum | cut -d' ' -f1)
mkdir "$CACHE/.${stage_id}.publish.A1b2C3"
mkdir "$CACHE/.${stage_id}.publish.D4e5F6"
mkdir "$CACHE/.${stage_id}.publish.A1b2C"
mkdir "$CACHE/.${stage_id}.publish.A1b2-3"
: > "$CACHE/.${stage_id}.publish.A1b2C3/.web-cache-stage"
web_cache_lock key
web_cache_publish key "$HARNESS_TMP/b.json"
web_cache_unlock
test ! -e "$CACHE/.${stage_id}.publish.A1b2C3"
test -d "$CACHE/.${stage_id}.publish.D4e5F6"
test -d "$CACHE/.${stage_id}.publish.A1b2C"
test -d "$CACHE/.${stage_id}.publish.A1b2-3"

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
'''
        )


if __name__ == "__main__":
    unittest.main()
