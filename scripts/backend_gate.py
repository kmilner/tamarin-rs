#!/usr/bin/env python3
"""backend_gate.py — regression gate for the proved-only algebra backend.

That the native backend answers correctly is a theorem. That it answers at
all, and how fast, is not, so this gate measures both against the Maude
backend of the same binary. It proves every theory of a list on both backends
(`--algebra-backend=maude` and `=proved-only`), each prover process under its
own memory cap and timeout, and fails when

  * a lemma's verdict on proved-only differs from Maude's (or the number of
    wellformedness warnings does), unless the row is listed in the verdict
    exceptions file with exactly that pair of verdicts;
  * a theory finishes on Maude but not on proved-only (nonzero exit, memory
    cap or timeout), unless it is listed in the pending file;
  * a theory that takes Maude longer than --min-ref-seconds (default 1 s)
    takes proved-only more than --max-ratio (default 2) times as long, taking
    the minimum over --runs runs of each backend, unless it is listed in the
    pending file;
  * a listed exception or pending entry no longer applies (so both files
    stay honest), or Maude itself does not finish (unless
    --allow-ref-failures).

Usage:
  scripts/backend_gate.py --smoke            # the CI job: ~30 theories, minutes
  scripts/backend_gate.py --full             # the whole corpus, manual/nightly
  scripts/backend_gate.py --list FILE ...    # any list

A list holds one theory per line, relative to the examples directory
(tamarin-prover/examples), optionally followed by a tab and extra prover
flags; `#` starts a comment. The exceptions and pending files name theories
by the same relative path. See TESTING.md, "Backend gate".

Results land in --out (default scripts/results/backend_gate/<mode>/, which
is gitignored): the stdout and stderr of every run, one JSON record per run,
and summary.tsv. The last line of output is
`DONE_BACKEND_GATE verdict=OK|FAIL ...`; the exit status is 0, 1 for a failed
gate, or 2 when the gate could not run.
"""

import argparse
import concurrent.futures
import json
import os
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GATE_DIR = os.path.join(REPO, "scripts", "backend_gate")
BACKENDS = ("maude", "proved-only")
NATIVE = "proved-only"

# `  name (all-traces): verified (12 steps)` in the summary of summaries.
LEMMA = re.compile(
    r"^\s+(\S+) \((all-traces|exists-trace)\): "
    r"(verified|falsified|analysis incomplete)(?:[^(]*\((\d+) steps\))?"
)
WELLFORMEDNESS = re.compile(r"WARNING: (\d+) wellformedness check failed")
NO_LEAN = "requires a build with --features lean-unification"


def die(message):
    print(f"backend_gate: {message}", file=sys.stderr)
    sys.exit(2)


def parse_size(text):
    """`6G`, `512M`, or bytes."""
    units = {"K": 1 << 10, "M": 1 << 20, "G": 1 << 30}
    text = text.strip().upper().removesuffix("IB").removesuffix("B")
    if text and text[-1] in units:
        return int(float(text[:-1]) * units[text[-1]])
    return int(text)


def data_lines(path):
    """The tab-separated fields of every line that is not blank or a comment."""
    rows = []
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            rows.append([field.strip() for field in line.split("\t")])
    return rows


def key_of(relative):
    """A directory name for a theory: its path without `../` and `.spthy`."""
    name = re.sub(r"^(\.\./)+", "", relative).replace("/", "__")
    return name.removesuffix(".spthy")


class Theory:
    def __init__(self, relative, flags, examples):
        self.relative = relative
        self.flags = shlex.split(flags)
        self.path = os.path.normpath(os.path.join(examples, relative))
        self.key = key_of(relative)


def read_list(path, examples):
    theories, seen = [], set()
    for fields in data_lines(path):
        theory = Theory(fields[0], fields[1] if len(fields) > 1 else "", examples)
        if theory.key in seen:
            die(f"{path}: {theory.relative} is listed twice")
        if not os.path.isfile(theory.path):
            die(f"{path}: no such theory: {theory.path}")
        seen.add(theory.key)
        theories.append(theory)
    if not theories:
        die(f"{path}: empty list")
    return theories


def read_exceptions(path):
    """{relative: {lemma: (maude verdict, native verdict)}}."""
    table = {}
    for fields in data_lines(path):
        if len(fields) < 5:
            die(f"{path}: expected theory, lemma, Maude verdict, native verdict, reason: {fields}")
        table.setdefault(fields[0], {})[fields[1]] = (fields[2], fields[3])
    return table


def read_pending(path):
    """{relative: reason}."""
    table = {}
    for fields in data_lines(path):
        if len(fields) < 2 or not fields[1]:
            die(f"{path}: a pending entry needs a reason: {fields}")
        table[fields[0]] = fields[1]
    return table


class Capper:
    """Runs one prover process under a memory cap and a timeout.

    `cgroup` puts the process and everything it starts in a transient systemd
    scope with MemoryMax, which bounds resident memory and lets a timeout kill
    the whole scope. `rlimit` bounds the address space of each process
    (RLIMIT_AS, what `ulimit -v` sets) and is the fallback where no user
    systemd instance is available, as on most CI runners.
    """

    def __init__(self, mode, mem_bytes):
        self.mem_bytes = mem_bytes
        self.serial = 0
        self.lock = threading.Lock()
        if mode == "auto":
            mode = "cgroup" if self.cgroup_works() else "rlimit"
        elif mode == "cgroup" and not self.cgroup_works():
            die("--mem-cap=cgroup: `systemd-run --user --scope` does not work here")
        self.mode = mode

    @staticmethod
    def cgroup_works():
        if not shutil.which("systemd-run"):
            return False
        probe = subprocess.run(
            ["systemd-run", "--user", "--scope", "-q", "true"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        return probe.returncode == 0

    def run(self, argv, cwd, stdout_path, stderr_path, timeout):
        """Returns (exit status, seconds, peak RSS in kB, timed out)."""
        unit = None
        preexec = None
        if self.mode == "cgroup":
            with self.lock:
                self.serial += 1
                unit = f"backend-gate-{os.getpid()}-{self.serial}.scope"
            argv = [
                "systemd-run", "--user", "--scope", "-q", "--expand-environment=no",
                f"--unit={unit}",
                "-p", f"MemoryMax={self.mem_bytes}", "-p", "MemorySwapMax=0",
            ] + argv
        elif self.mode == "rlimit":
            limit = self.mem_bytes

            def preexec():
                resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
                resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

        timed_out = threading.Event()
        with open(stdout_path, "wb") as out, open(stderr_path, "wb") as err:
            start = time.monotonic()
            process = subprocess.Popen(
                argv, cwd=cwd, stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                start_new_session=True, preexec_fn=preexec,
            )

            def signal_all(signum):
                try:
                    os.killpg(process.pid, signum)
                except ProcessLookupError:
                    pass
                if unit:
                    subprocess.run(
                        ["systemctl", "--user", "kill", f"--signal={signum}", unit],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
                    )

            def expire():
                timed_out.set()
                signal_all(signal.SIGTERM)
                hard = threading.Timer(5, signal_all, [signal.SIGKILL])
                hard.daemon = True
                hard.start()

            timer = threading.Timer(timeout, expire)
            timer.daemon = True
            timer.start()
            try:
                _, status, usage = os.wait4(process.pid, 0)
            finally:
                timer.cancel()
            seconds = time.monotonic() - start
            process.returncode = os.waitstatus_to_exitcode(status)
        # Helpers the prover left behind (a Maude in its own process group).
        if unit:
            subprocess.run(
                ["systemctl", "--user", "kill", "--signal=KILL", unit],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
            )
        code = 124 if timed_out.is_set() else process.returncode
        return code, seconds, usage.ru_maxrss, timed_out.is_set()


class Gate:
    def __init__(self, args, theories, exceptions, pending, capper, maude):
        self.args = args
        self.theories = theories
        self.exceptions = exceptions
        self.pending = pending
        self.capper = capper
        self.maude = maude
        self.records = {}  # (key, backend) -> [record per run]
        self.print_lock = threading.Lock()

    def record_path(self, theory, backend, index):
        return os.path.join(self.args.out, theory.key, f"{backend}.run{index}")

    def command(self, theory, backend):
        argv = [self.args.bin, f"--algebra-backend={backend}"]
        if backend == "maude":
            argv.append(f"--with-maude={self.maude}")
        argv += ["--derivcheck-timeout=30", "--processors=1"]
        argv += self.args.prover_arg + theory.flags + ["--prove", theory.path]
        return argv

    def run_one(self, theory, backend, index):
        base = self.record_path(theory, backend, index)
        if self.args.resume and os.path.isfile(base + ".json"):
            with open(base + ".json", encoding="utf-8") as handle:
                return json.load(handle)
        os.makedirs(os.path.dirname(base), exist_ok=True)
        timeout = self.args.timeout
        if backend == NATIVE and theory.relative in self.pending:
            timeout = min(timeout, self.args.pending_timeout)
        argv = self.command(theory, backend)
        code, seconds, rss, timed_out = self.capper.run(
            argv, os.path.dirname(theory.path), base + ".out", base + ".err", timeout
        )
        record = {
            "theory": theory.relative, "backend": backend, "run": index,
            "rc": code, "seconds": round(seconds, 3), "max_rss_kb": rss,
            "timed_out": timed_out, "timeout": timeout, "command": shlex.join(argv),
        }
        with open(base + ".json", "w", encoding="utf-8") as handle:
            json.dump(record, handle)
        if self.args.verbose:
            with self.print_lock:
                print(f"  ran {backend:<11} {seconds:7.2f}s rc={code:<3} {theory.relative}", flush=True)
        return record

    def run_all(self):
        with concurrent.futures.ThreadPoolExecutor(self.args.jobs) as pool:
            # Every theory once on each backend.
            first = {
                (theory.key, backend): pool.submit(self.run_one, theory, backend, 0)
                for theory in self.theories
                for backend in BACKENDS
            }
            for slot, future in first.items():
                self.records[slot] = [future.result()]
            # The timing rule reads the minimum over --runs runs. It applies
            # only where Maude takes longer than the threshold, and the
            # minimum cannot exceed the first run, so only those theories
            # can need the further runs.
            again = {}
            for theory in self.theories:
                ref = self.records[(theory.key, "maude")][0]
                native = self.records[(theory.key, NATIVE)][0]
                timed = ref["rc"] == 0 and native["rc"] == 0
                if timed and ref["seconds"] > self.args.min_ref_seconds:
                    for backend in BACKENDS:
                        again[(theory.key, backend)] = [
                            pool.submit(self.run_one, theory, backend, index)
                            for index in range(1, self.args.runs)
                        ]
            for slot, futures in again.items():
                self.records[slot] += [future.result() for future in futures]

    def results(self, theory, backend):
        """The lemma rows of the first run, with the wellformedness count."""
        rows = []
        path = self.record_path(theory, backend, 0) + ".out"
        with open(path, encoding="utf-8", errors="replace") as handle:
            text = handle.read()
        # The summary follows the last rule of `=`; lemma text above it may
        # hold lines of the same shape.
        summary = text[text.rfind("summary of summaries:"):]
        for line in summary.splitlines():
            match = LEMMA.match(line)
            if match:
                rows.append((match.group(1), match.group(2), match.group(3), match.group(4)))
        warnings = WELLFORMEDNESS.findall(summary)
        rows.append(("<wellformedness warnings>", "", warnings[0] if warnings else "0", None))
        return rows

    def best(self, theory, backend):
        runs = [r["seconds"] for r in self.records[(theory.key, backend)] if r["rc"] == 0]
        return min(runs) if runs else None

    def failure_of(self, record):
        if record["timed_out"]:
            return f"timeout after {record['timeout']}s"
        with open(
            self.record_path_of(record) + ".err", encoding="utf-8", errors="replace"
        ) as handle:
            lines = [line.strip() for line in handle if line.strip()]
        tail = lines[-1][:160] if lines else "no stderr"
        return f"rc={record['rc']}: {tail}"

    def record_path_of(self, record):
        return os.path.join(
            self.args.out, key_of(record["theory"]), f"{record['backend']}.run{record['run']}"
        )

    def judge(self):
        """One row per theory: (status, theory, Maude s, native s, detail)."""
        rows = []
        for theory in self.theories:
            ref = self.records[(theory.key, "maude")][0]
            native = self.records[(theory.key, NATIVE)][0]
            pending = self.pending.get(theory.relative)
            excepted = self.exceptions.get(theory.relative, {})
            ref_s, native_s = self.best(theory, "maude"), self.best(theory, NATIVE)

            def row(status, detail="", ref_s=ref_s, native_s=native_s, theory=theory):
                rows.append((status, theory.relative, ref_s, native_s, detail))

            if native["rc"] != 0:
                with open(
                    self.record_path(theory, NATIVE, 0) + ".err", encoding="utf-8", errors="replace"
                ) as handle:
                    if NO_LEAN in handle.read():
                        die(f"{self.args.bin} was built without --features lean-unification")
            if ref["rc"] != 0:
                status = "REF_FAIL_OK" if self.args.allow_ref_failures else "REF_FAIL"
                native_end = "finished" if native["rc"] == 0 else self.failure_of(native)
                row(status, f"Maude: {self.failure_of(ref)}; proved-only: {native_end}")
                continue
            if native["rc"] != 0:
                reason = self.failure_of(native)
                if pending:
                    row("XFAIL", f"{reason} (pending: {pending})")
                else:
                    row("NATIVE_FAIL", reason)
                continue

            ref_rows, native_rows = self.results(theory, "maude"), self.results(theory, NATIVE)
            ref_verdicts = [r[:3] for r in ref_rows]
            native_verdicts = [r[:3] for r in native_rows]
            if ref_verdicts != native_verdicts:
                differing = self.differences(ref_verdicts, native_verdicts)
                unexplained = [
                    f"{name}: Maude {a}, proved-only {b}"
                    for name, a, b in differing
                    if excepted.get(name) != (a, b)
                ]
                stale = sorted(set(excepted) - {name for name, _, _ in differing})
                if unexplained:
                    row("VERDICT_DIFF", "; ".join(unexplained))
                    continue
                if stale:
                    row("STALE_EXCEPTION", "no longer differs: " + ", ".join(stale))
                    continue
                verdict_note = "listed exception: " + ", ".join(
                    f"{name} ({a} / {b})" for name, a, b in differing
                )
            elif excepted:
                row("STALE_EXCEPTION", "the verdicts agree; remove it from the exceptions file")
                continue
            else:
                verdict_note = ""

            slow = (
                ref_s > self.args.min_ref_seconds and native_s > self.args.max_ratio * ref_s
            )
            if slow:
                detail = f"{native_s / ref_s:.2f}x Maude over {len(self.records[(theory.key, NATIVE)])} runs"
                if pending:
                    row("XFAIL", f"{detail} (pending: {pending})")
                else:
                    row("SLOW", detail)
                continue
            if pending:
                row("XPASS", "finishes within the limits; remove it from the pending file")
                continue
            steps = [
                f"{a[0]} {a[3]}/{b[3]}"
                for a, b in zip(ref_rows, native_rows)
                if a[3] != b[3]
            ]
            note = verdict_note
            if steps and self.args.steps:
                note = "; ".join(filter(None, [note, "steps " + ", ".join(steps)]))
            row("EXCEPTION" if verdict_note else ("OK_STEPS" if steps else "OK"), note)

        ran = {theory.relative for theory in self.theories}
        if self.args.strict_lists:
            for name in sorted((set(self.pending) | set(self.exceptions)) - ran):
                rows.append(("NOT_RUN", name, None, None, "listed as pending or excepted, not in the list"))
        return rows

    @staticmethod
    def differences(ref, native):
        """(lemma, Maude verdict, native verdict) for every row that differs."""
        ref_map = {(name, kind): verdict for name, kind, verdict in ref}
        native_map = {(name, kind): verdict for name, kind, verdict in native}
        out = []
        for slot in dict.fromkeys(list(ref_map) + list(native_map)):
            a, b = ref_map.get(slot, "absent"), native_map.get(slot, "absent")
            if a != b:
                out.append((slot[0], a, b))
        if not out:
            # The same rows in another order.
            out.append(("<lemma order>", "as listed", "reordered"))
        return out


FAILING = {
    "VERDICT_DIFF": "verdict differs from Maude",
    "NATIVE_FAIL": "finishes on Maude but not on proved-only",
    "SLOW": "slower than the allowed ratio",
    "REF_FAIL": "Maude did not finish",
    "XPASS": "pending entry that now passes",
    "STALE_EXCEPTION": "verdict exception that no longer applies",
    "NOT_RUN": "pending or excepted theory missing from the list",
}


def report(gate, rows, elapsed):
    args = gate.args
    order = ["VERDICT_DIFF", "NATIVE_FAIL", "SLOW", "REF_FAIL", "XPASS", "STALE_EXCEPTION",
             "NOT_RUN", "XFAIL", "EXCEPTION", "REF_FAIL_OK", "OK_STEPS", "OK"]
    counts = {status: 0 for status in order}
    for status, *_ in rows:
        counts[status] += 1

    def seconds(value):
        return "-" if value is None else f"{value:.2f}"

    with open(os.path.join(args.out, "summary.tsv"), "w", encoding="utf-8") as handle:
        handle.write("status\ttheory\tmaude_s\tnative_s\tratio\tdetail\n")
        for status, name, ref_s, native_s, detail in rows:
            ratio = f"{native_s / ref_s:.2f}" if ref_s and native_s else "-"
            handle.write(f"{status}\t{name}\t{seconds(ref_s)}\t{seconds(native_s)}\t{ratio}\t{detail}\n")

    print(f"\n=== backend gate: {len(gate.theories)} theories, proved-only against Maude ===")
    print(f"{'status':<16}{'maude':>8}{'native':>8}{'ratio':>7}  theory")
    shown = rows if args.verbose else [r for r in rows if r[0] not in ("OK", "OK_STEPS")]
    for status, name, ref_s, native_s, detail in sorted(shown, key=lambda r: order.index(r[0])):
        ratio = f"{native_s / ref_s:.2f}" if ref_s and native_s else "-"
        print(f"{status:<16}{seconds(ref_s):>8}{seconds(native_s):>8}{ratio:>7}  {name}")
        if detail:
            print(f"{'':<16}{detail}")

    timed = [(n / r, name, r, n) for _, name, r, n, _ in rows
             if r and n and r > args.min_ref_seconds]
    ref_total = sum(r for _, _, r, n, _ in rows if r and n)
    native_total = sum(n for _, _, r, n, _ in rows if r and n)
    print("\n=== SUMMARY ===")
    print(f"both finished: {sum(1 for _, _, r, n, _ in rows if r and n)}"
          f"   Maude total {ref_total:.1f}s   proved-only total {native_total:.1f}s")
    print(f"timing rule: native <= {args.max_ratio:g}x Maude where Maude > "
          f"{args.min_ref_seconds:g}s, minimum of {args.runs} run(s); it applied to {len(timed)} theories")
    for ratio, name, ref_s, native_s in sorted(timed, reverse=True)[:5]:
        print(f"  {ratio:5.2f}x  Maude {ref_s:.2f}s  proved-only {native_s:.2f}s  {name}")
    print("  ".join(f"{status}={counts[status]}" for status in order if counts[status]))
    failed = {status: counts[status] for status in FAILING if counts[status]}
    for status, count in failed.items():
        print(f"FAIL {status}={count}: {FAILING[status]}")
    verdict = "FAIL" if failed else "OK"
    tail = "".join(f" {status}={count}" for status, count in failed.items())
    print(f"per-process caps: {args.mem} memory ({gate.capper.mode}), {args.timeout}s; "
          f"jobs {args.jobs}; wall {elapsed:.0f}s; results in {args.out}")
    print(f"DONE_BACKEND_GATE verdict={verdict} theories={len(gate.theories)}"
          f" xfail={counts['XFAIL']} exceptions={counts['EXCEPTION']}{tail}")
    return 1 if failed else 0


def resolve_maude(explicit):
    path = explicit or os.environ.get("MAUDE_PATH") or shutil.which("maude")
    if not path or not os.access(path, os.X_OK):
        die("no Maude: pass --maude, set MAUDE_PATH, or put `maude` on PATH")
    return os.path.abspath(path)


def resolve_bin(explicit):
    candidates = [explicit] if explicit else [
        os.environ.get("RS_PATH"),
        os.path.join(REPO, "target", "ci", "tamarin-rs"),
        os.path.join(REPO, "target", "release", "tamarin-rs"),
    ]
    for candidate in candidates:
        if candidate and os.access(candidate, os.X_OK):
            return os.path.abspath(candidate)
    die("no prover binary: build with --features lean-unification and pass --bin (or set RS_PATH)")


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--smoke", action="store_true",
                      help="the smoke list: 3 runs, 60 s timeout (what CI runs)")
    mode.add_argument("--full", action="store_true",
                      help="the whole corpus: 1 run, 300 s timeout, Maude failures reported only")
    parser.add_argument("--list", help="theory list (default: the mode's list)")
    parser.add_argument("--bin", help="prover binary built with lean-unification "
                        "(default: $RS_PATH, target/ci/tamarin-rs, target/release/tamarin-rs)")
    parser.add_argument("--out", help="results directory (default: scripts/results/backend_gate/<mode>)")
    parser.add_argument("--examples", default=os.path.join(REPO, "tamarin-prover", "examples"),
                        help="directory the list's paths are relative to")
    parser.add_argument("--maude", help="Maude binary (default: $MAUDE_PATH, then PATH)")
    parser.add_argument("--jobs", type=int, default=2, help="prover processes at a time (default 2)")
    parser.add_argument("--timeout", type=float, help="seconds per prover process")
    parser.add_argument("--pending-timeout", type=float, default=20,
                        help="proved-only timeout for a pending theory (default 20)")
    parser.add_argument("--mem", default="6G", help="memory cap per prover process (default 6G)")
    parser.add_argument("--mem-cap", choices=["auto", "cgroup", "rlimit"], default="auto",
                        help="how the cap is enforced: a systemd scope (resident memory) or "
                        "RLIMIT_AS (address space); auto prefers the scope")
    parser.add_argument("--runs", type=int, help="runs per backend for the timing rule (minimum is used)")
    parser.add_argument("--min-ref-seconds", type=float, default=1.0,
                        help="the timing rule applies above this Maude time (default 1)")
    parser.add_argument("--max-ratio", type=float, default=2.0,
                        help="allowed proved-only / Maude time (default 2)")
    parser.add_argument("--exceptions", default=os.path.join(GATE_DIR, "verdict_exceptions.tsv"))
    parser.add_argument("--pending", default=os.path.join(GATE_DIR, "pending.tsv"))
    parser.add_argument("--allow-ref-failures", action="store_true", default=None,
                        help="report a theory Maude does not finish instead of failing")
    parser.add_argument("--resume", action="store_true",
                        help="reuse the runs already recorded in --out")
    parser.add_argument("--prover-arg", action="append", default=[],
                        help="extra argument for every prover run (repeatable)")
    parser.add_argument("--steps", action="store_true", help="list step-count differences")
    parser.add_argument("--verbose", "-v", action="store_true", help="print every run and every row")
    args = parser.parse_args()

    name = "full" if args.full else "smoke" if args.smoke or not args.list else "custom"
    preset = {
        "smoke": dict(list="smoke.tsv", runs=3, timeout=60.0, allow=False),
        "full": dict(list="corpus.tsv", runs=1, timeout=300.0, allow=True),
        "custom": dict(list=None, runs=1, timeout=300.0, allow=False),
    }[name]
    # An entry of the pending or exceptions file that the list does not
    # contain is an error only for the two lists that are meant to hold them.
    args.strict_lists = args.list is None
    args.list = args.list or os.path.join(GATE_DIR, preset["list"])
    args.runs = args.runs or preset["runs"]
    args.timeout = args.timeout or preset["timeout"]
    if args.allow_ref_failures is None:
        args.allow_ref_failures = preset["allow"]
    args.out = os.path.abspath(args.out or os.path.join(REPO, "scripts", "results", "backend_gate", name))
    if args.jobs < 1 or args.runs < 1:
        die("--jobs and --runs must be positive")

    args.bin = resolve_bin(args.bin)
    maude = resolve_maude(args.maude)
    os.environ["PATH"] = os.path.dirname(maude) + os.pathsep + os.environ.get("PATH", "")
    theories = read_list(args.list, os.path.abspath(args.examples))
    exceptions = read_exceptions(args.exceptions)
    pending = read_pending(args.pending)
    capper = Capper(args.mem_cap, parse_size(args.mem))
    os.makedirs(args.out, exist_ok=True)

    print(f"backend gate ({name}): {len(theories)} theories from {os.path.relpath(args.list, REPO)}")
    print(f"binary {args.bin}\nMaude  {maude}")
    print(f"caps   {args.mem} ({capper.mode}), {args.timeout:g}s per process, {args.jobs} at a time")
    sys.stdout.flush()

    gate = Gate(args, theories, exceptions, pending, capper, maude)
    start = time.monotonic()
    gate.run_all()
    rows = gate.judge()
    sys.exit(report(gate, rows, time.monotonic() - start))


if __name__ == "__main__":
    main()
