#!/usr/bin/env python3
"""Compare two corpus_raw_diff TSVs by (file, lemma) verdict.
Usage: compare_parity_tsv.py baseline.tsv after.tsv
Cols: file, lemma, status(MATCH/DIFF/SKIP_*), hs_lines, rs_lines, diff_lines, note, ms
Reports regressions (MATCH->DIFF) and improvements (DIFF->MATCH); ignores SKIP rows
(timeouts can't be compared) but flags MATCH->SKIP as a possible perf regression.
"""
import csv, sys

def load(p):
    d = {}
    for r in csv.reader(open(p), delimiter='\t'):
        if len(r) < 3:
            continue
        d[(r[0], r[1])] = r[2]
    return d

base, after = load(sys.argv[1]), load(sys.argv[2])
reg, imp, m2skip, new_diff = [], [], [], []
for k, bs in base.items():
    as_ = after.get(k)
    if as_ is None:
        continue
    if bs == 'MATCH' and as_ == 'DIFF':
        reg.append(k)
    elif bs == 'DIFF' and as_ == 'MATCH':
        imp.append(k)
    elif bs == 'MATCH' and as_.startswith('SKIP'):
        m2skip.append(k)
# lemmas newly DIFF that weren't comparable before (were SKIP) — informational
for k, as_ in after.items():
    if as_ == 'DIFF' and base.get(k, '').startswith('SKIP'):
        new_diff.append(k)

def cnt(d, s):
    return sum(1 for v in d.values() if v == s)

print(f"baseline: {cnt(base,'MATCH')} MATCH / {cnt(base,'DIFF')} DIFF")
print(f"after:    {cnt(after,'MATCH')} MATCH / {cnt(after,'DIFF')} DIFF")
print(f"\n*** REGRESSIONS (MATCH->DIFF): {len(reg)} ***")
for f, l in reg:
    print(f"  REG  {f.split('/examples/')[-1]}::{l}")
print(f"\nimprovements (DIFF->MATCH): {len(imp)}")
for f, l in imp:
    print(f"  IMP  {f.split('/examples/')[-1]}::{l}")
print(f"\nMATCH->SKIP (possible perf regression to investigate): {len(m2skip)}")
for f, l in m2skip[:40]:
    print(f"  S->  {f.split('/examples/')[-1]}::{l}")
print(f"\nwas-SKIP now-DIFF (informational, newly comparable): {len(new_diff)}")
sys.exit(1 if reg else 0)
