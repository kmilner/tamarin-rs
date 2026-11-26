#!/usr/bin/env python3
"""End-to-end caller-scope check: small theories whose lemma variables are named like
unifier witnesses, proved on every algebra backend and against a renamed twin.

A lemma's verdict may depend neither on the backend nor on what its variables are called.
Each generated theory has an AC term in an action (so its rule variants enter the equation
store as a disjunction) and lemmas whose quantified variables are bystanders of that
disjunction. The twin is the same theory with the lemma variables renamed to names no
witness uses.

usage: audit_scope_theories.py --bin PATH/tamarin-rs --out DIR [--seed S] [--count N]
                               [--backends maude,proved-only] [--timeout SECS] [--jobs J]
                               [--families xor,diffie-hellman,multiset,bilinear-pairing]

Without --families the theories use xor and diffie-hellman, as they always did; with it
each theory draws its builtin uniformly from the list.
Exit status 1 if any verdict differs.
"""
import argparse
import concurrent.futures
import itertools
import os
import random
import re
import subprocess
import sys

XOR_TERMS = ["x XOR y", "x XOR y XOR 'c'", "<x XOR y, y>", "h(x XOR y)", "x XOR h(y)"]
DH_TERMS = ["'g'^x^y", "'g'^(x*y)", "'g'^(x*inv(y))", "<'g'^x, 'g'^(x*y)>"]
MSET_TERMS = ["x ++ y", "<x ++ y, y>", "h(x ++ y)", "x ++ y ++ 'c'"]
BP_TERMS = ["em(x, y)", "pmult(x, 'P')", "em(pmult(x, 'P'), y)", "<pmult(x, y), 'g'^x>"]
FAMILIES = {
    "xor": XOR_TERMS,
    "diffie-hellman": DH_TERMS,
    "multiset": MSET_TERMS,
    "bilinear-pairing": BP_TERMS,
}
WITNESS_NAMES = ["x", "y", "z", "x1", "x2"]
PLAIN_NAMES = ["q", "r", "s", "t", "w"]


def theory(name, builtins, term, marks, lemma_vars, conclusion):
    """`marks` bystander messages per Mark fact; `lemma_vars` their names in the lemmas."""
    ms = ["m%d" % i for i in range(marks)]
    tup = ms[0] if marks == 1 else "<" + ", ".join(ms) + ">"
    vs = lemma_vars[:marks]
    concl = conclusion.format(v=vs[0], w=vs[-1])
    fns = "functions: h/1\n" if "h(" in term else ""
    return f"""theory {name}
begin
builtins: {builtins}
{fns}rule Init: [ Fr(~a), Fr(~b) ] --> [ St(~a, ~b) ]
rule R: [ St(x, y) ] --[ Act({term}), Other(x, y) ]-> [ ]
rule M: [ In({tup}) ] --[ Mark({", ".join(ms)}) ]-> [ ]
lemma all_traces:
  "All c e {" ".join(vs)} #i #j. Other(c, e) @ i & Mark({", ".join(vs)}) @ j ==> {concl}"
lemma some_trace: exists-trace
  "Ex c e {" ".join(vs)} #i #j. Other(c, e) @ i & Mark({", ".join(vs)}) @ j & not({concl})"
end
"""


CONCLUSIONS = ["{v} = c", "{v} = e", "not({v} = c)", "{v} = {w}", "({v} = c) | ({w} = e)"]


def generate(rng, n, families=None):
    cases = []
    for i in range(n):
        if families:
            builtins = rng.choice(families)
            term = rng.choice(FAMILIES[builtins])
        elif rng.random() < 0.6:
            builtins, term = "xor", rng.choice(XOR_TERMS)
        else:
            builtins, term = "diffie-hellman", rng.choice(DH_TERMS)
        marks = rng.choice([1, 1, 2, 3])
        # Witnesses are called `x`; the other names only vary the binding order.
        names = rng.sample(WITNESS_NAMES[1:], marks)
        if rng.random() < 0.75:
            names[rng.randrange(marks)] = "x"
        concl = rng.choice(CONCLUSIONS)
        cases.append(
            (
                "S%d" % i,
                theory("S%d" % i, builtins, term, marks, names, concl),
                theory("S%d" % i, builtins, term, marks, PLAIN_NAMES, concl),
                f"{builtins}; Act({term}); lemma vars {names}; {concl}",
            )
        )
    return cases


VERDICT = re.compile(r"^\s*(all_traces|some_trace) \((?:all-traces|exists-trace)\): (verified|falsified)", re.M)


def prove(binary, backend, path, timeout):
    try:
        p = subprocess.run(
            [binary, "--prove", "--algebra-backend=" + backend, path],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
            text=True,
        )
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    found = dict(VERDICT.findall(p.stdout))
    if len(found) != 2:
        return "ERROR(exit %d)" % p.returncode
    return "%s/%s" % (found["all_traces"], found["some_trace"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=40)
    ap.add_argument("--backends", default="maude,proved-only")
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--families", default="")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    backends = a.backends.split(",")
    families = [f for f in a.families.split(",") if f]
    cases = generate(random.Random(a.seed), a.count, families)
    jobs = {}
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for name, text, twin, _ in cases:
            for tag, body in (("orig", text), ("twin", twin)):
                path = os.path.join(a.out, f"{name}_{tag}.spthy")
                with open(path, "w") as f:
                    f.write(body)
                for b in backends:
                    jobs[(name, tag, b)] = pool.submit(prove, a.bin, b, path, a.timeout)
    bad = 0
    undecided = 0
    histogram = {}
    for name, _, _, desc in cases:
        res = {(tag, b): jobs[(name, tag, b)].result() for tag, b in itertools.product(("orig", "twin"), backends)}
        for key, r in res.items():
            histogram[(key[1], r)] = histogram.get((key[1], r), 0) + 1
        if len(set(res.values())) != 1:
            bad += 1
            print(f"DIFFERENCE {name}: {desc}")
            for (tag, b), r in sorted(res.items()):
                print(f"    {tag:4} {b:12} {r}")
        elif any(r.startswith(("TIMEOUT", "ERROR")) for r in res.values()):
            # Agreement on "no verdict" compares nothing.
            undecided += 1
            print(f"UNDECIDED {name}: {desc}: {sorted(set(res.values()))}")
    for (b, r), n in sorted(histogram.items()):
        print(f"    {b:12} {r:24} {n}")
    print(
        f"{len(cases)} theories x 2 namings x {len(backends)} backends: "
        f"{bad} with a verdict difference, {undecided} without a verdict on any backend"
    )
    return 1 if bad or undecided else 0


if __name__ == "__main__":
    sys.exit(main())
