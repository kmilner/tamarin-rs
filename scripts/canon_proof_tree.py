#!/usr/bin/env python3
"""Canonicalize tamarin proof tree to structural form."""
import sys
import re

def strip_balanced(s, start, opening='(', closing=')'):
    depth = 0
    i = start
    while i < len(s):
        if s[i] == opening: depth += 1
        elif s[i] == closing:
            depth -= 1
            if depth == 0: return i + 1
        i += 1
    return len(s)

text = sys.stdin.read()
# Strip dump_proof header
text = re.sub(r'^=== .*===\s*$', '', text, flags=re.MULTILINE)
# Strip HS comment blocks /* ... */
out = []
i = 0
while i < len(text):
    if text[i:i+2] == '/*':
        end = text.find('*/', i+2)
        if end == -1: break
        i = end + 2
    else:
        out.append(text[i])
        i += 1
text = ''.join(out)

# Replace `solve( ... )` (with balanced parens) with `solve`
out = []
i = 0
while i < len(text):
    if text[i:i+6] == 'solve(':
        end = strip_balanced(text, i+5)
        out.append('solve')
        i = end
    else:
        out.append(text[i])
        i += 1
text = ''.join(out)

# Normalize "by solve" -> "by contradiction"
text = re.sub(r'by solve\b', 'by contradiction', text)
text = re.sub(r'by contradiction[^\n]*', 'by contradiction', text)

# Strip trailing "end" + summary
text = re.sub(r'\nend\s*\n.*$', '', text, flags=re.DOTALL)

# Strip trailing theory boilerplate (restrictions, rules, etc.) that HS
# re-prints after the lemma's proof tree. dump_proof emits only the
# proof tree, so this content has no counterpart on the Rust side.
text = re.sub(r'\n(restriction|rule|lemma|axiom|functions|equations|builtins|predicates|tactic|configuration|heuristic|options)[ \t][^\n]*\n.*$', '\n', text, flags=re.DOTALL)

# Identify the proof tree by finding the first line that starts a method
# (induction, solve, simplify, by, or other proof-tree keywords).
# Drop everything before the first such line (skips lemma headers / quoted formulas).
lines = text.splitlines()
proof_kw_re = re.compile(r'^\s*(induction|solve|simplify|by\b|SOLVED)')
start_idx = 0
for idx, ln in enumerate(lines):
    if proof_kw_re.match(ln):
        start_idx = idx
        break
lines = lines[start_idx:]

# Drop empty/whitespace-only lines, normalize trailing whitespace
lines = [ln.rstrip() for ln in lines if ln.strip()]
print('\n'.join(lines))
