#!/usr/bin/env python3
"""Regression tests for scripts/backend_gate.py.

They run the gate against a stand-in prover whose behaviour on each backend
is chosen by the theory's file name, so every rule of the gate is exercised
in a few seconds without Maude or the Lean library:

    python3 scripts/test_backend_gate.py
"""

import os
import stat
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
GATE = os.path.join(HERE, "backend_gate.py")

# The stand-in prover: `<name>.spthy` selects the behaviour, the backend the
# branch. It prints the part of the output the gate reads.
PROVER = r"""#!/usr/bin/env bash
backend=maude
for arg in "$@"; do
    case "$arg" in --algebra-backend=*) backend=${arg#*=} ;; esac
    theory=$arg
done
name=$(basename "$theory" .spthy)
verdict="verified (3 steps)"
case "$name:$backend" in
    differs:proved-only) verdict="falsified - found trace (4 steps)" ;;
    steps:proved-only) verdict="verified (5 steps)" ;;
    hangs:proved-only) sleep 60 ;;
    crashes:proved-only) echo "error: proved-only backend does not support this" >&2; exit 1 ;;
    slow:maude) sleep 1.2 ;;
    slow:proved-only) sleep 3.2 ;;
    refdead:maude) echo "error: maude died" >&2; exit 1 ;;
esac
warning=
[ "$name:$backend" = warns:proved-only ] && warning="  WARNING: 1 wellformedness check failed!"
cat <<EOF
theory T begin
  lemma (all-traces): verified (99 steps)
end
==============================================================================
summary of summaries:

analyzed: $theory

  processing time: 0.01s

$warning
  lemma_a (all-traces): $verdict
  lemma_b (exists-trace): verified (2 steps)

==============================================================================
EOF
"""


class BackendGate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="backend-gate-test-")
        root = cls.tmp.name
        cls.examples = os.path.join(root, "examples")
        os.makedirs(cls.examples)
        cls.prover = os.path.join(root, "prover")
        with open(cls.prover, "w", encoding="utf-8") as handle:
            handle.write(PROVER)
        os.chmod(cls.prover, os.stat(cls.prover).st_mode | stat.S_IXUSR)
        # Any executable serves as the Maude the stand-in never starts.
        cls.maude = cls.prover
        for name in ["fine", "differs", "steps", "hangs", "crashes", "slow", "refdead", "warns"]:
            with open(os.path.join(cls.examples, f"{name}.spthy"), "w", encoding="utf-8") as handle:
                handle.write("theory T begin end\n")
        cls.serial = 0

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def write(self, name, lines):
        path = os.path.join(self.tmp.name, name)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write("# comment\n\n" + "".join(line + "\n" for line in lines))
        return path

    def gate(self, theories, pending=(), exceptions=(), extra=()):
        """Run the gate; return (exit status, {theory: status}, output)."""
        BackendGate.serial += 1
        out = os.path.join(self.tmp.name, f"out{BackendGate.serial}")
        command = [
            sys.executable, GATE,
            "--list", self.write("list.tsv", [f"{name}.spthy" for name in theories]),
            "--pending", self.write("pending.tsv", pending),
            "--exceptions", self.write("exceptions.tsv", exceptions),
            "--examples", self.examples, "--bin", self.prover, "--maude", self.maude,
            "--out", out, "--timeout", "2", "--pending-timeout", "1", "--jobs", "4",
            "--mem", "2G", *extra,
        ]
        done = subprocess.run(command, capture_output=True, text=True, check=False)
        statuses = {}
        summary = os.path.join(out, "summary.tsv")
        if os.path.isfile(summary):
            with open(summary, encoding="utf-8") as handle:
                for line in handle.read().splitlines()[1:]:
                    fields = line.split("\t")
                    statuses[fields[1].removesuffix(".spthy")] = fields[0]
        return done.returncode, statuses, done.stdout + done.stderr

    def test_agreeing_backends_pass(self):
        code, statuses, output = self.gate(["fine", "steps"])
        self.assertEqual(code, 0, output)
        self.assertEqual(statuses, {"fine": "OK", "steps": "OK_STEPS"})
        self.assertIn("DONE_BACKEND_GATE verdict=OK theories=2", output)

    def test_verdict_difference_fails_unless_listed_exactly(self):
        code, statuses, output = self.gate(["differs", "warns"])
        self.assertEqual(code, 1, output)
        self.assertEqual(statuses, {"differs": "VERDICT_DIFF", "warns": "VERDICT_DIFF"})
        self.assertIn("lemma_a: Maude verified, proved-only falsified", output)
        self.assertIn("DONE_BACKEND_GATE verdict=FAIL", output)

        listed = ["differs.spthy\tlemma_a\tverified\tfalsified\tnative is right"]
        code, statuses, output = self.gate(["differs"], exceptions=listed)
        self.assertEqual((code, statuses), (0, {"differs": "EXCEPTION"}), output)

        other = ["differs.spthy\tlemma_a\tfalsified\tverified\tthe opposite pair"]
        code, statuses, output = self.gate(["differs"], exceptions=other)
        self.assertEqual((code, statuses), (1, {"differs": "VERDICT_DIFF"}), output)

        # A pending entry never excuses a verdict.
        code, statuses, output = self.gate(["differs"], pending=["differs.spthy\thangs"])
        self.assertEqual((code, statuses), (1, {"differs": "VERDICT_DIFF"}), output)

    def test_stale_exception_fails(self):
        listed = ["fine.spthy\tlemma_a\tverified\tfalsified\tfixed since"]
        code, statuses, output = self.gate(["fine"], exceptions=listed)
        self.assertEqual((code, statuses), (1, {"fine": "STALE_EXCEPTION"}), output)

    def test_native_failure_fails_unless_pending(self):
        code, statuses, output = self.gate(["hangs", "crashes", "fine"])
        self.assertEqual(code, 1, output)
        self.assertEqual(
            statuses, {"hangs": "NATIVE_FAIL", "crashes": "NATIVE_FAIL", "fine": "OK"}
        )
        self.assertIn("timeout after 2", output)
        self.assertIn("does not support this", output)

        pending = ["hangs.spthy\tvariants do not terminate", "crashes.spthy\tunsupported"]
        code, statuses, output = self.gate(["hangs", "crashes", "fine"], pending=pending)
        self.assertEqual(code, 0, output)
        self.assertEqual(statuses, {"hangs": "XFAIL", "crashes": "XFAIL", "fine": "OK"})
        # The pending timeout applies to the native run of a pending theory.
        self.assertIn("timeout after 1", output)
        self.assertIn("xfail=2", output)

    def test_pending_entry_that_passes_fails(self):
        code, statuses, output = self.gate(["fine"], pending=["fine.spthy\tfixed since"])
        self.assertEqual((code, statuses), (1, {"fine": "XPASS"}), output)

    def test_slowdown_beyond_the_ratio_fails(self):
        code, statuses, output = self.gate(
            ["slow"], extra=["--timeout", "20", "--runs", "2"]
        )
        self.assertEqual((code, statuses), (1, {"slow": "SLOW"}), output)
        self.assertIn("over 2 runs", output)

        code, statuses, output = self.gate(
            ["slow"], extra=["--timeout", "20", "--max-ratio", "4"]
        )
        self.assertEqual((code, statuses), (0, {"slow": "OK"}), output)

        # Below the reference threshold the rule does not apply.
        code, statuses, output = self.gate(
            ["slow"], extra=["--timeout", "20", "--min-ref-seconds", "2"]
        )
        self.assertEqual((code, statuses), (0, {"slow": "OK"}), output)

    def test_reference_failure_fails_unless_allowed(self):
        code, statuses, output = self.gate(["refdead"])
        self.assertEqual((code, statuses), (1, {"refdead": "REF_FAIL"}), output)
        code, statuses, output = self.gate(["refdead"], extra=["--allow-ref-failures"])
        self.assertEqual((code, statuses), (0, {"refdead": "REF_FAIL_OK"}), output)

    def test_resume_reuses_recorded_runs(self):
        out = os.path.join(self.tmp.name, "resumed")
        first = self.gate(["fine"], extra=["--out", out])
        record = os.path.join(out, "fine", "proved-only.run0.json")
        before = os.stat(record).st_mtime_ns
        second = self.gate(["fine"], extra=["--out", out, "--resume"])
        self.assertEqual((first[0], second[0]), (0, 0), second[2])
        self.assertEqual(os.stat(record).st_mtime_ns, before)

    def test_shipped_lists_are_consistent(self):
        """Every pending and excepted theory is in the smoke and full lists."""
        gate_dir = os.path.join(HERE, "backend_gate")

        def first_fields(name):
            with open(os.path.join(gate_dir, name), encoding="utf-8") as handle:
                return [
                    line.split("\t")[0].strip()
                    for line in handle
                    if line.strip() and not line.startswith("#")
                ]

        smoke, full = first_fields("smoke.tsv"), first_fields("corpus.tsv")
        self.assertEqual(len(smoke), len(set(smoke)))
        self.assertEqual(len(full), len(set(full)))
        self.assertLessEqual(set(smoke), set(full))
        for name in first_fields("pending.tsv") + first_fields("verdict_exceptions.tsv"):
            self.assertIn(name, smoke)
        for name in smoke:
            if name.startswith("../../"):
                path = os.path.normpath(os.path.join(HERE, "..", name.removeprefix("../../")))
                self.assertTrue(os.path.isfile(path), path)


if __name__ == "__main__":
    unittest.main()
