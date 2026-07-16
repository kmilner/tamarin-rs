#!/usr/bin/env python3
"""Pretty-print block-level differences between two canonicalized trace
files. Useful for tracking which solveGoal blocks have rule-iteration
mismatches between HS and Rust.

Usage:
    diff_trace.py <hs.trace> <rs.trace>

Outputs a per-block summary:
    Block N: <solveGoal header>
      ✓ matching (set equal)
      ✗ HS-only rules: [...]
      ✗ RS-only rules: [...]

Operates on raw traces — internally runs canonicalize_trace.py in
`groups` mode to align rule iteration.
"""
import sys
from collections import Counter


def parse_blocks(path):
    """Read a trace file and yield (header_line, [rule_names], [body_lines])."""
    header = None
    rules = []
    body = []
    current_rule = None
    current_rule_body = []

    def flush():
        nonlocal current_rule, current_rule_body
        if current_rule is not None:
            rules.append(current_rule)
            body.extend(current_rule_body)
        current_rule = None
        current_rule_body = []

    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line.startswith("[EXEC]"):
                continue
            if line.startswith("[EXEC] solveGoal"):
                if header is not None:
                    flush()
                    yield (header, rules, body)
                header = line
                rules = []
                body = []
                current_rule = None
                current_rule_body = []
            elif line.startswith("[EXEC] exploitPrems rule="):
                flush()
                rule_name = line.split("rule=", 1)[1]
                current_rule = rule_name
                current_rule_body = [line]
            else:
                if current_rule is not None:
                    current_rule_body.append(line)
                elif header is not None:
                    body.append(line)
    if header is not None:
        flush()
        yield (header, rules, body)


def aggregate_by_header(blocks):
    """Group blocks by solveGoal header, summing rule iteration counts.
    Lets two traces with different block ORDER still compare correctly
    on a per-header basis."""
    agg = {}
    for header, rules, _body in blocks:
        c = agg.setdefault(header, Counter())
        c.update(rules)
    return agg


def main():
    if len(sys.argv) != 3:
        sys.stderr.write("usage: diff_trace.py <hs.trace> <rs.trace>\n")
        sys.exit(2)
    hs_blocks = list(parse_blocks(sys.argv[1]))
    rs_blocks = list(parse_blocks(sys.argv[2]))

    hs_by_header = aggregate_by_header(hs_blocks)
    rs_by_header = aggregate_by_header(rs_blocks)

    all_headers = sorted(set(hs_by_header.keys()) | set(rs_by_header.keys()))
    matched = 0
    set_mismatch = 0
    count_mismatch = 0
    hs_only_blocks = 0
    rs_only_blocks = 0

    for header in all_headers:
        h_rules = hs_by_header.get(header, Counter())
        r_rules = rs_by_header.get(header, Counter())

        if h_rules == r_rules:
            matched += 1
            continue

        if header not in hs_by_header:
            rs_only_blocks += 1
            tag = "RS-ONLY-BLOCK"
        elif header not in rs_by_header:
            hs_only_blocks += 1
            tag = "HS-ONLY-BLOCK"
        elif set(h_rules.keys()) == set(r_rules.keys()):
            count_mismatch += 1
            tag = "COUNT"
        else:
            set_mismatch += 1
            tag = "SET"

        h_only = h_rules - r_rules
        r_only = r_rules - h_rules
        print(f"[{tag}] {header}")
        if h_only:
            extras = ", ".join(f"{n}x {name}" for name, n in sorted(h_only.items()))
            print(f"  HS-only:  {extras}")
        if r_only:
            extras = ", ".join(f"{n}x {name}" for name, n in sorted(r_only.items()))
            print(f"  RS-only:  {extras}")

    print()
    print(f"Total unique headers: {len(all_headers)}")
    print(f"  matching:        {matched}")
    print(f"  set mismatch:    {set_mismatch}")
    print(f"  count mismatch:  {count_mismatch}")
    print(f"  HS-only blocks:  {hs_only_blocks}")
    print(f"  RS-only blocks:  {rs_only_blocks}")


if __name__ == "__main__":
    main()
