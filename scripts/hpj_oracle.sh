#!/bin/bash
# Render a HughesPJ document with the REAL `pretty-1.1.3.6` — the library
# `crates/tamarin-theory/src/pretty_hpj.rs` ports — so an HPJ layout
# expectation can be DERIVED instead of captured from the port.
#
# Why this exists.  Every other oracle in `scripts/` is the patched
# tamarin-prover binary, and reaching a specific `Doc` shape through it means
# finding a theory that produces one.  HPJ is the exception: the layout
# engine is an ordinary Haskell library, GHC 9.6.7 ships exactly the version
# the port targets, and a `Doc` expression is three lines.  So the raw
# combinator pins in `pretty_hpj_tests.rs` cost a compile each rather than a
# corpus hunt, and "wrapping happened" assertions (`contains('\n')`,
# `starts_with`) have no excuse.
#
# Usage:
#   scripts/hpj_oracle.sh 'sep [text "aaaaaa", text "bbbbbb"]'    # 110/73
#   scripts/hpj_oracle.sh -w 5 -r 5 'sep [text "aaaaaa", text "bbbbbb"]'
#   scripts/hpj_oracle.sh --one-line '<expr>'
#   scripts/hpj_oracle.sh --file Cases.hs   # a whole Main, run verbatim
#   scripts/hpj_oracle.sh --self-test       # prove the toolchain first
#   scripts/hpj_oracle.sh --emit-template   # the generated Main, to stdout
#
# The expression is Haskell, evaluated with `Text.PrettyPrint.HughesPJ` in
# scope and `Prelude`'s `<>` hidden (HughesPJ exports its own).  Read it from
# stdin by passing `-` instead.
#
# Widths.  `-w`/`-r` are lineLength and RIBBON WIDTH, the same two numbers
# `Doc::render_with(w, r)` takes; the style's `ribbonsPerLine` is `w/r`, which
# is how the port's constants are stated too (`RIBBON = round(110/1.5) = 73`).
# The defaults, 110/73, are HS's CONSOLE width (`Main/Console.hs`'s
# `renderDoc`) and so are what a bare `Doc::render()` uses on the CLI path;
# the interactive server renders at HughesPJ's own default 100/67, and
# `pretty_hpj.rs` names both pairs.
#
# pretty_hpj.rs       this script
# ------------------- ------------------------------------------------------
# render_with(w, r)   -w w -r r                    (PageMode)
# render()            the defaults, 110/73         (CLI path)
# render(), server    -w 100 -r 67                 (after set_display_width)
# one_line_render()   --one-line                   (OneLineMode)
# render_at(..)       NO public-API equivalent: it calls pretty's internal
#                     `get1` with a starting column, which HughesPJ does not
#                     export.  Derive the surrounding Doc instead.
#
# Env:
#   HPJ_GHC=<path>          compiler to use.  Set-but-unusable is a HARD
#                           fail, never a silent fall-through to another one.
#   HPJ_ALLOW_ANY_PRETTY=1  proceed when the resolved compiler's `pretty` is
#                           not 1.1.3.6.  Off by default because a document
#                           rendered by a different layout engine is not an
#                           oracle byte — it is a plausible-looking wrong
#                           answer, and it would enter the tree as a pin.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# The shared plumbing, for the OOM prologue; a consumer that cannot read it
# exits 2 rather than falling back to a private copy (see gate_common.sh).
[ -r "$SCRIPT_DIR/gate_common.sh" ] || {
    echo "cannot read $SCRIPT_DIR/gate_common.sh" >&2; exit 2; }
# shellcheck source=gate_common.sh
. "$SCRIPT_DIR/gate_common.sh"

# The pretty the port reproduces.  `pretty_hpj.rs` cites this version by name
# throughout ("pretty-1.1.3.6 `Text.PrettyPrint.HughesPJ`"), and its layout
# has changed across releases, so the version is part of what makes an answer
# here an oracle byte at all.
WANT_PRETTY=1.1.3.6
# The GHC that ships it here: the one `./setup.sh testing` already installs to
# build the oracle, so no second toolchain is needed.  Tried only after
# $HPJ_GHC and a `ghc` on PATH, so an operator's own wins over this path --
# the same last-resort shape as `gate_common.sh`'s linuxbrew maude.
STACK_GHC="${HOME:-/root}/.stack/programs/x86_64-linux/ghc-tinfo6-9.6.7/bin/ghc"

W=110
R=73
MODE=PageMode
EXPR=
FILE=
SELFTEST=0
EMIT_TEMPLATE=0

die() { echo "hpj_oracle.sh: $*" >&2; exit 2; }

usage() { sed -n '2,/^set -uo/p' "${BASH_SOURCE[0]}" | sed 's/^# \?//;$d'; }

while [ $# -gt 0 ]; do
    case "$1" in
        -w) W="${2:?-w needs a line length}"; shift 2 ;;
        -r) R="${2:?-r needs a ribbon width}"; shift 2 ;;
        --one-line) MODE=OneLineMode; shift ;;
        --file) FILE="${2:?--file needs a path}"; shift 2 ;;
        --self-test) SELFTEST=1; shift ;;
        --emit-template) EMIT_TEMPLATE=1; shift ;;
        -h|--help) usage; exit 0 ;;
        -) EXPR="$(cat)"; shift ;;
        --) shift; EXPR="${1-}"; break ;;
        -*) die "unknown option $1 (try --help)" ;;
        *) EXPR="$1"; shift ;;
    esac
done

case "$W$R" in *[!0-9]*) die "-w and -r take positive integers (got w=$W r=$R)" ;; esac
[ "$W" -gt 0 ] && [ "$R" -gt 0 ] || die "-w and -r must be positive (got w=$W r=$R)"

# --- toolchain resolution ----------------------------------------------------
resolve_ghc() {
    if [ -n "${HPJ_GHC:-}" ]; then
        # Set-but-unusable is the failure the maude resolver exists to stop:
        # falling through to a DIFFERENT compiler would answer from a pretty
        # the operator did not choose, and say nothing about it.
        command -v "$HPJ_GHC" >/dev/null 2>&1 \
            || die "HPJ_GHC=$HPJ_GHC is set but not executable"
        echo "$HPJ_GHC"
        return
    fi
    if command -v ghc >/dev/null 2>&1; then command -v ghc; return; fi
    if [ -x "$STACK_GHC" ]; then echo "$STACK_GHC"; return; fi
    die "no GHC. Tried, in order: \$HPJ_GHC (unset), ghc on PATH, $STACK_GHC"
}

# The pretty in the compiler's package db, or empty if it has none.
pretty_version() {
    local ghc="$1" pkg
    pkg="$(dirname "$ghc")/ghc-pkg"
    [ -x "$pkg" ] || pkg="$(command -v ghc-pkg 2>/dev/null)"
    [ -n "$pkg" ] && [ -x "$pkg" ] || return 0
    "$pkg" --simple-output list pretty 2>/dev/null | tr ' ' '\n' \
        | sed -n 's/^pretty-//p' | tail -1
}

GHC="$(resolve_ghc)" || exit 2
HAVE_PRETTY="$(pretty_version "$GHC")"
if [ "$HAVE_PRETTY" != "$WANT_PRETTY" ]; then
    msg="$GHC ships pretty-${HAVE_PRETTY:-<none>}, not $WANT_PRETTY"
    if [ "${HPJ_ALLOW_ANY_PRETTY:-0}" = 1 ]; then
        echo "WARNING: $msg — HPJ_ALLOW_ANY_PRETTY=1: these bytes are NOT an" >&2
        echo "         oracle expectation; do not commit them as one." >&2
    else
        die "$msg. HPJ_ALLOW_ANY_PRETTY=1 overrides, but its output is then not the layout engine the port reproduces."
    fi
fi

# --- the generated program ---------------------------------------------------
# Written in three pieces so the user's expression never passes through shell
# expansion: Haskell operators are `$$`, `$+$`, `<>`, and an unquoted heredoc
# would eat every one of them.
emit_main() {
    cat <<HS_HEAD
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ
import System.IO

-- \`ribbonsPerLine\` is lineLength/ribbonWidth, so -w/-r are the same two
-- numbers \`Doc::render_with\` takes.
theStyle :: Style
theStyle = style { mode = $MODE
                 , lineLength = $W
                 , ribbonsPerLine = fromIntegral ($W :: Int)
                                    / fromIntegral ($R :: Int) }
HS_HEAD
    cat <<'HS_MID'

-- Rust string-literal escaping.  The point of the RUST line is that it pastes
-- into an `assert_eq!`, and Haskell's own `show` escapes non-ASCII to decimal
-- (`\8743` for the port's `∧`), which Rust does not accept.  So the escape set
-- here is exactly Rust's and every other character goes out as UTF-8.
rustEsc :: String -> String
rustEsc = concatMap esc
  where
    esc '\\' = "\\\\"
    esc '"'  = "\\\""
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc '\r' = "\\r"
    esc c    = [c]

report :: Doc -> IO ()
report d = do
  hSetEncoding stdout utf8
  let s = renderStyle theStyle d
  putStrLn ("RUST\t\"" ++ rustEsc s ++ "\"")
  -- Raw, between markers, because trailing spaces are load-bearing in this
  -- engine (an `fsep` can leave one before its break) and invisible otherwise.
  putStrLn "--- raw ---"
  putStr s
  putStrLn ""
  putStrLn "--- end ---"

theDoc :: Doc
theDoc =
HS_MID
    printf '%s\n' "  ( $EXPR )"
    cat <<'HS_TAIL'

main :: IO ()
main = report theDoc
HS_TAIL
}

# render <workdir> -> compiles and runs, echoing the program's stdout
run_program() {
    local dir="$1" src="$2" out rc
    (
        oom_prologue 16777216
        exec timeout "${HPJ_TIMEOUT:-300}" \
            "$GHC" -v0 -outputdir "$dir/build" "$src" -o "$dir/prog"
    )
    rc=$?
    [ $rc -eq 0 ] || { echo "hpj_oracle.sh: GHC failed (exit $rc)" >&2; return $rc; }
    ( oom_prologue 16777216; exec timeout "${HPJ_TIMEOUT:-300}" "$dir/prog" )
}

WORK=
cleanup() { [ -n "$WORK" ] && rm -rf "$WORK"; }
trap cleanup EXIT

# --- self-test ---------------------------------------------------------------
# Every case is one of the port's own committed assertions, re-derived here.
# They check the TOOLCHAIN, not the layout: if a case disagrees, either this
# script is not driving the pretty the port reproduces or the port has
# regressed, and until that is resolved nothing derived in the session is
# worth committing.  Run it before deriving a pin you intend to keep.
#
# The last case is the only one whose RIBBON differs from its line length,
# and it is here because of a probe: multiplying the generated style's
# ribbon by 4 left the five equal-width cases all matching.  Every knob this
# script plumbs into `theStyle` needs a case that moves when it moves.
SELFTEST_PASS=0
SELFTEST_FAIL=0

# expect <w> <r> <expr> <want>
expect() {
    local w="$1" r="$2" expr="$3" want="$4" got
    got="$(W="$w" R="$r" MODE=PageMode EXPR="$expr" derive)" \
        || { SELFTEST_FAIL=$((SELFTEST_FAIL+1)); return; }
    if [ "$got" = "$want" ]; then
        SELFTEST_PASS=$((SELFTEST_PASS+1))
    else
        SELFTEST_FAIL=$((SELFTEST_FAIL+1))
        echo "MISMATCH  (w=$w r=$r)  $expr" >&2
        echo "   the port asserts:      $want" >&2
        echo "   pretty-$HAVE_PRETTY renders: $got" >&2
    fi
}

self_test() {
    # crates/tamarin-theory/src/pretty_hpj_tests.rs
    expect 5 5 'sep [text "aaaaaa", text "bbbbbb"]' \
        '"aaaaaa\nbbbbbb"'
    expect 6 6 'sep [text "aaa", sep [text "bbb", text "ccc"]]' \
        '"aaa\nbbb\nccc"'
    expect 10 10 'sep [text "aaaaaaaaaa", text "bbbbbbbbbb"]' \
        '"aaaaaaaaaa\nbbbbbbbbbb"'
    expect 10 10 \
        'sep [text "Q.", sep [nest 1 (text "DANTE"), text "c", nest 1 (text "DSUCC")]]' \
        '"Q.\n DANTE\nc\n DSUCC"'
    expect 12 12 \
        'fcat [text "<", text "aaa,", text "bbb,", text "ccc,", text "ddd", text ">"]' \
        '"<aaa,bbb,\nccc,ddd>"'
    # crates/tamarin-theory/src/pretty_hpj_sep_nb_regression_tests.rs
    # (nested_sep_disjunct_second_item_column) — width 50, ribbon 33.
    expect 50 33 \
        'let opp d = text "(" <> d <> text ")"; fa a = sep [text "F.", sep [nest 1 (opp (text a)), text "=>", nest 1 (text "RHS")]]; dj l = sep [text ("Q" ++ l ++ "."), sep [nest 1 (opp (text "DANTE")), text "C", nest 1 (sep [opp (fa (replicate 32 (head "A"))) <> text " &", opp (fa (replicate 32 (head "B")))])]] in text "(" <> sep (punctuate (text " |") [opp (dj "x"), opp (dj "y")]) <> text ")"' \
        '"((Qx.\n   (DANTE)\n  C\n   (F.\n     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)\n    =>\n     RHS) &\n   (F.\n     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)\n    =>\n     RHS)) |\n (Qy.\n   (DANTE)\n  C\n   (F.\n     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)\n    =>\n     RHS) &\n   (F.\n     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)\n    =>\n     RHS)))"'

    echo "self-test: $SELFTEST_PASS matched, $SELFTEST_FAIL failed" \
         "(pretty-$HAVE_PRETTY via $GHC)"
    [ "$SELFTEST_FAIL" -eq 0 ] || return 1
    # A case list that silently emptied would print "0 matched, 0 failed" and
    # exit 0, which is the one result this check must never give.
    [ "$SELFTEST_PASS" -gt 0 ] || { echo "self-test compared nothing" >&2; return 1; }
}

# derive -> just the RUST line's literal, for the self-test's comparison
derive() {
    local d
    d="$(mktemp -d)" || return 1
    emit_main > "$d/Main.hs"
    run_program "$d" "$d/Main.hs" | sed -n 's/^RUST\t//p'
    local rc=${PIPESTATUS[0]}
    rm -rf "$d"
    return "$rc"
}

if [ "$EMIT_TEMPLATE" = 1 ]; then
    EXPR="${EXPR:-empty}"
    emit_main
    exit 0
fi

if [ "$SELFTEST" = 1 ]; then
    self_test
    exit $?
fi

WORK="$(mktemp -d)" || die "mktemp failed"

if [ -n "$FILE" ]; then
    # Whole-Main mode: a derivation session with shared bindings and a dozen
    # cases is a Haskell file, not a shell argument.  Run verbatim — the
    # widths above do not apply, the file states its own.
    [ -r "$FILE" ] || die "cannot read --file $FILE"
    cp "$FILE" "$WORK/Main.hs"
    run_program "$WORK" "$WORK/Main.hs"
    exit $?
fi

[ -n "$EXPR" ] || die "no expression (pass one, or \`-\` to read stdin, or --file)"
emit_main > "$WORK/Main.hs"
run_program "$WORK" "$WORK/Main.hs"
exit $?
