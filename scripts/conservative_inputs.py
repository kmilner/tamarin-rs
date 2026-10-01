#!/usr/bin/env python3
"""Conservative, parser-independent theory dependency discovery.

This intentionally over-approximates the active preprocessor branch.  Only
dependencies that exist are emitted: the real parser remains responsible for
diagnosing an active missing include, while this scanner prevents a parser bug
that omits an existing input from making a cache key stale.
"""

from __future__ import annotations

import os
import pathlib
import re
import shlex
import sys


INCLUDE = re.compile(r"#\s*include\b[^\"\n]*\"([^\"\n]+)\"")
QUOTED = re.compile(r'"([^"\n]+)"')
ORACLE_HEURISTIC = re.compile(r"(?:\bheuristic\s*[:=]|--heuristic=)[^\n]*\bo\b")


def row(tag: str, source: pathlib.Path, rel: str) -> None:
    # Match the parser manifest's reversible, delimiter-safe Unix path fields.
    # os.fsencode preserves surrogate-escaped filesystem bytes.
    source_field = "x:" + os.fsencode(source).hex()
    rel_field = "x:" + os.fsencode(rel).hex()
    print(f"{tag}\t{source_field}\t{rel_field}")


def main() -> int:
    if len(sys.argv) < 2:
        return 2
    root = pathlib.Path(sys.argv[1]).resolve()
    flags = " ".join(sys.argv[2:])
    base = root.parent
    pending: list[tuple[pathlib.Path, str]] = [(root, root.name)]
    seen: set[tuple[pathlib.Path, pathlib.Path]] = set()
    sources: list[tuple[pathlib.Path, str, str]] = []
    oracles: set[tuple[pathlib.Path, str]] = set()

    def add_oracle(candidate: pathlib.Path, alias: str | None = None) -> None:
        if not candidate.is_file():
            return
        resolved = candidate.resolve()
        if alias is None:
            relative = os.path.relpath(resolved, base)
            alias = "" if relative == ".." or relative.startswith("../") else relative
        oracles.add((resolved, alias))

    while pending:
        source, alias = pending.pop()
        canonical = source.resolve()
        # Includes are relative to the path used to open the fragment, even
        # when that fragment is a symlink. The same file opened from another
        # directory can therefore have different dependencies.
        identity = (canonical, source.parent.resolve())
        if identity in seen or not canonical.is_file():
            continue
        seen.add(identity)
        text = source.read_text(errors="replace")
        sources.append((source, alias, text))
        for match in INCLUDE.finditer(text):
            spelling = match.group(1)
            child = source.parent / spelling
            if child.is_file():
                child_alias = os.path.normpath(
                    os.path.join(os.path.dirname(alias), spelling)
                )
                pending.append((child, child_alias))

    for source, alias, text in sources:
        source_dir = source.parent
        alias_dir = os.path.dirname(alias)
        # Deliberately broader than the grammar: an accidentally omitted
        # heuristic must not also make its neighbouring oracle disappear from
        # the independent cache identity.
        for candidate in source_dir.glob("oracle*"):
            add_oracle(candidate)
        if ORACLE_HEURISTIC.search(text) or ORACLE_HEURISTIC.search(flags):
            # Haskell's default name uses the prefix before the first dot.
            base_name = source.name.split(".", 1)[0]
            default = source.with_name(base_name + ".oracle")
            rel = os.path.normpath(os.path.join(alias_dir, default.name))
            add_oracle(default, rel)
        # Quoted heuristic paths are a small subset of all quoted strings.
        # Treating every existing executable quoted path as an oracle is a safe
        # over-approximation and avoids duplicating the parser grammar here.
        for spelling in QUOTED.findall(text):
            candidate = (source_dir / spelling).resolve()
            if candidate.is_file() and os.access(candidate, os.X_OK):
                rel = os.path.normpath(os.path.join(alias_dir, spelling))
                add_oracle(candidate, rel)

    for candidate in pathlib.Path.cwd().glob("oracle*"):
        add_oracle(candidate)

    try:
        words = shlex.split(flags)
    except ValueError:
        words = flags.split()
    explicit_oracles: list[str] = []
    next_is_oracle = False
    for word in words:
        if next_is_oracle:
            explicit_oracles.append(word)
            next_is_oracle = False
            continue
        if word.startswith("--oraclename="):
            explicit_oracles.append(word.split("=", 1)[1])
        elif word == "--oraclename":
            next_is_oracle = True
    for explicit_oracle in explicit_oracles:
        candidate = pathlib.Path(explicit_oracle)
        if not candidate.is_absolute():
            candidate = base / candidate
        add_oracle(candidate)

    row("S", root, root.name)
    for source, alias, _ in sorted(sources[1:], key=lambda item: (item[1], str(item[0]))):
        row("S", source, alias)
    for source, alias in sorted(oracles, key=lambda item: (item[1], str(item[0]))):
        row("O", source, alias)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
