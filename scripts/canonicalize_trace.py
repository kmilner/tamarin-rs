#!/usr/bin/env python3
"""Canonicalize a tamarin-prover EXEC trace by sorting rule-iteration
groups alphabetically within each `[EXEC] solveGoal` block.

HS's lazy ListT / parList rdeepseq enumeration produces non-deterministic
rule iteration order. To diff HS vs Rust traces meaningfully, both sides
must be canonicalized to the same order. After canonicalization, traces
should be byte-identical for blocks where HS and Rust iterate the same
SET of rules; remaining diffs surface genuine rule-set divergences.

Usage:
    canonicalize_trace.py [--mode=groups|sort|multiset] < trace > canonical

Modes:
    groups    Group lines into rule-iteration sub-blocks (default).
              Sorts rule groups by name; preserves within-group order.
              Best for diff'ing HS vs Rust traces that share rule
              iteration structure.
    sort      Sort ALL lines alphabetically within each solveGoal block.
              Maximally canonical; loses ordering info but cancels
              line-position non-determinism from lazy IO.
    multiset  Per block, output (sorted unique line, count) pairs.
              Compares the multiset of events without ordering info.

The default `groups` mode strips non-`[EXEC]` lines (status banners,
progress markers) so prefix differences between HS and Rust don't
pollute the diff.
"""
import sys
import argparse
from collections import Counter


def parse_blocks(lines):
    """Yield (header_lines, rule_groups, in_block_tail) per solveGoal block.

    Returns triples:
      header_lines: list[str] — solveGoal anchor + any leading non-rule lines.
      rule_groups: list[(rule_name, [lines])] — each starts at
        `[EXEC] exploitPrems rule=X` and includes follow-up lines until
        the next exploitPrems or block end.
      in_block_tail: list[str] — trailing lines after the last rule group
        (not currently used; kept for symmetry).
    """
    pending_header = []
    current_block_header = None
    current_groups = []
    current_group = None

    def flush_block():
        if current_block_header is not None:
            groups = current_groups[:]
            if current_group is not None:
                groups.append(current_group)
            return (current_block_header, groups, [])
        return None

    for raw in lines:
        line = raw.rstrip("\n")
        if not line.startswith("[EXEC]"):
            # Non-exec output (status lines, banners): drop entirely.
            # HS/Rust prefix banners differ trivially and aren't part of
            # the canonical trace semantics.
            continue

        if line.startswith("[EXEC] solveGoal"):
            blk = flush_block()
            if blk is not None:
                yield blk
            current_block_header = pending_header + [line]
            pending_header = []
            current_groups = []
            current_group = None
        elif line.startswith("[EXEC] exploitPrems rule="):
            if current_group is not None:
                current_groups.append(current_group)
            rule_name = line.split("rule=", 1)[1]
            current_group = (rule_name, [line])
        else:
            if current_group is not None:
                current_group[1].append(line)
            elif current_block_header is not None:
                # in-block line before any rule group — append to header.
                current_block_header.append(line)
            else:
                pending_header.append(line)

    blk = flush_block()
    if blk is not None:
        yield blk
    elif pending_header:
        yield (pending_header, [], [])


def canonicalize_groups(lines):
    out = []
    for header, groups, _ in parse_blocks(lines):
        out.extend(header)
        # Sort rule groups by (rule_name, body) — secondary key keeps
        # duplicate rule-name groups in a stable order.
        sorted_groups = sorted(groups, key=lambda g: (g[0], g[1]))
        for _, body in sorted_groups:
            out.extend(body)
    return out


def canonicalize_sort(lines):
    """Sort all lines within each solveGoal block (anchor line kept first)."""
    out = []
    for header, groups, _ in parse_blocks(lines):
        # Anchor is header[0] when it starts with `[EXEC] solveGoal`.
        anchor = []
        rest = []
        for h in header:
            if h.startswith("[EXEC] solveGoal") and not anchor:
                anchor.append(h)
            else:
                rest.append(h)
        block_lines = rest[:]
        for _, body in groups:
            block_lines.extend(body)
        out.extend(anchor)
        out.extend(sorted(block_lines))
    return out


def canonicalize_multiset(lines):
    """Per block, emit (count, line) pairs sorted lexicographically."""
    out = []
    for header, groups, _ in parse_blocks(lines):
        anchor = []
        rest = []
        for h in header:
            if h.startswith("[EXEC] solveGoal") and not anchor:
                anchor.append(h)
            else:
                rest.append(h)
        block_lines = rest[:]
        for _, body in groups:
            block_lines.extend(body)
        out.extend(anchor)
        counts = Counter(block_lines)
        for line in sorted(counts.keys()):
            n = counts[line]
            out.append(f"{n}x {line}")
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["groups", "sort", "multiset"],
                        default="groups")
    args = parser.parse_args()

    lines = sys.stdin.readlines()
    if args.mode == "groups":
        canonical = canonicalize_groups(lines)
    elif args.mode == "sort":
        canonical = canonicalize_sort(lines)
    else:
        canonical = canonicalize_multiset(lines)
    print("\n".join(canonical))


if __name__ == "__main__":
    main()
