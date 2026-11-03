#!/usr/bin/env python3
"""Run upstream command sidecars against Rust using upstream's assertions.

Public entry point: scripts/test.sh regressions. No Haskell executable or
oracle cache is used: expected diagnostics and verdicts come from the patched
upstream sources. Every discovered scenario is run or reported as out of scope.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import copy
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import time


REPO = Path(__file__).resolve().parent.parent


def load_runner(root):
    spec = importlib.util.spec_from_file_location(
        "regressionTestCommands", root / "regressionTestCommands.py")
    runner = importlib.util.module_from_spec(spec)
    # Importing must not add __pycache__ to the generated oracle worktree:
    # setup.sh would treat it as a source change and reapply the patch series.
    previous = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        spec.loader.exec_module(runner)
    finally:
        sys.dont_write_bytecode = previous
    return runner


def exclusion(args):
    # Classify individual commands, not filenames: a theory can have both
    # trace and diff scenarios, and negated-equivalence is a trace regression.
    if any(arg == "--diff" or arg.startswith("--diff=") for arg in args):
        return "diff mode is outside the Rust parity scope"
    for index, arg in enumerate(args):
        module = None
        if arg.startswith(("--output-module=", "-m=")):
            module = arg.split("=", 1)[1]
        elif arg in ("--output-module", "-m") and index + 1 < len(args):
            module = args[index + 1]
        if module in ("proverif", "proverifequiv", "deepsec"):
            return f"{module} exporter is not implemented in Rust"
    return None


def rust_case(relative, case):
    case = copy.deepcopy(case)
    # Clap requires '=' for optional short values. Preserve all configurations.
    case["args"] = [re.sub(r"^-D(?!=)(.+)$", r"-D=\1", arg)
                    for arg in case.get("args", [])]
    # These parser diagnostics use codespan, not Parsec. Keep the rejection
    # and offending-token assertions; fail if upstream changes the assertion
    # instead of silently replacing a newly strengthened check.
    diagnostics = {
        "regression/negative/issue905-undeclared-em.spthy":
            ('unexpected "("', ["error: Undeclared function", "declare function `em` before using it"]),
        "regression/negative/issue906-end-prefix.spthy":
            ("unexpected", ["error: Unknown theory item `endrule`"]),
        "regression/negative/missing-end.spthy":
            ("unexpected end of input", ["error:", 'expected theory item, "end"; found end of input']),
    }
    if relative.as_posix() in diagnostics:
        old, new = diagnostics[relative.as_posix()]
        if case.get("contains") != [old] or case.get("exit_code") != 1:
            raise ValueError(f"Review the Rust diagnostic adapter for {relative}")
        case["contains"] = new
    return case


def discover(root, runner):
    cases, excluded = [], []
    for sidecar in sorted((root / "examples").rglob("*.spthy.test.json")):
        source = Path(str(sidecar).removesuffix(".test.json"))
        relative = source.relative_to(root / "examples")
        if not source.is_file():
            raise ValueError(f"Missing theory: {source}")
        document = json.loads(sidecar.read_text(encoding="utf-8"))
        if (not isinstance(document, dict) or set(document) != {"tests"}
                or not isinstance(document["tests"], list) or not document["tests"]):
            raise ValueError(f"Expected a non-empty tests list: {sidecar}")
        names = set()
        for original in document["tests"]:
            runner.validate(original)
            name = original["name"]
            if name in names:
                raise ValueError(f"Duplicate scenario {name}: {sidecar}")
            names.add(name)
            label = f"{relative.as_posix()}::{name}"
            reason = exclusion(original.get("args", []))
            if reason:
                excluded.append({"case": label, "reason": reason})
                continue
            case = rust_case(relative, original)
            baseline_dir = root / "case-studies-regression"
            if not case.get("slow"):
                baseline_dir /= "fast-tests"
            if case.get("checks") and "baseline" not in case:
                case["baseline"] = str(relative.with_name(relative.stem + "_analyzed.spthy"))
            if "baseline" in case:
                # Fail before running anything if a roundtrip/proof comparison
                # cannot be made. Never fall back to today's Rust output.
                runner.verdicts((baseline_dir / case["baseline"]).read_text(encoding="utf-8"))
            cases.append((label, source, case, baseline_dir))
    if not cases:
        raise ValueError("No supported upstream command scenarios discovered")
    return cases, excluded


def run(root, binary, jobs, results):
    runner = load_runner(root)
    cases, excluded = discover(root, runner)
    results.mkdir(parents=True, exist_ok=True)
    print(f"Upstream regressions: {len(cases)} scenarios, {len(excluded)} exclusions; {results}", flush=True)
    for item in excluded:
        print(f"EXCLUDED {item['case']}: {item['reason']}", flush=True)

    def check(item):
        label, source, case, baseline_dir = item
        artifacts = results / source.relative_to(root / "examples") / case["name"]
        started = time.monotonic()
        error = None
        try:
            runner.run_test(source, case, str(binary), baseline_dir, artifacts)
        except (OSError, runner.RegressionFailure) as failure:
            error = str(failure)
            artifacts.mkdir(parents=True, exist_ok=True)
            (artifacts / "failure.txt").write_text(error + "\n", encoding="utf-8")
        return {"case": label, "seconds": round(time.monotonic() - started, 3),
                "error": error}

    started = time.monotonic()
    outcomes = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for future in as_completed([pool.submit(check, item) for item in cases]):
            outcome = future.result()
            outcomes.append(outcome)
            status = "FAIL" if outcome["error"] else "PASS"
            print(f"{status} {outcome['case']} ({outcome['seconds']:.1f}s)", flush=True)
    failures = sum(item["error"] is not None for item in outcomes)
    seconds = round(time.monotonic() - started, 3)
    (results / "results.json").write_text(json.dumps({
        "binary": str(binary), "seconds": seconds,
        "results": sorted(outcomes, key=lambda item: item["case"]),
        "excluded": excluded,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Upstream regressions: {len(cases) - failures}/{len(cases)} passed, "
          f"{len(excluded)} excluded, {seconds:.1f}s; results: {results}", flush=True)
    return int(bool(failures))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO / "tamarin-prover-testing")
    parser.add_argument("--binary", type=Path, default=REPO / "target/release/tamarin-rs")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--results", type=Path)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if not args.binary.is_file() or not os.access(args.binary, os.X_OK):
        parser.error(f"No executable Rust binary: {args.binary}; build first")
    if args.results is None:
        parent = Path(os.environ.get("RESULTS_ROOT", REPO / "scripts/results"))
        parent.mkdir(parents=True, exist_ok=True)
        args.results = Path(tempfile.mkdtemp(prefix="regressions.", dir=parent))
    return run(args.root.resolve(), args.binary.resolve(), args.jobs, args.results.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
