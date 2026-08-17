#!/bin/bash
# Render a HughesPJ document with the actual `pretty-1.1.3.6` library.
# `crates/tamarin-theory/src/pretty_hpj.rs` ports that library.  This script
# lets you derive an HPJ layout expectation instead of capturing it from the
# port.
#
# Why this exists.  Every other oracle in `scripts/` is the patched
# tamarin-prover binary.  To reach a given `Doc` shape through that binary,
# you must find a theory that produces the shape.  HPJ is the exception.  The
# layout engine is an ordinary Haskell library.  GHC 9.6.7 ships exactly the
# version that the port targets.  A `Doc` expression is three lines long.
# Therefore each raw combinator pin in `pretty_hpj_tests.rs` costs one compile
# instead of a search through the corpus.  There is then no reason to write an
# assertion that only shows that wrapping occurred (`contains('\n')`,
# `starts_with`).
#
# Usage:
#   scripts/hpj_oracle.sh 'sep [text "aaaaaa", text "bbbbbb"]'    # 110/73
#   scripts/hpj_oracle.sh -w 5 -r 5 'sep [text "aaaaaa", text "bbbbbb"]'
#   scripts/hpj_oracle.sh --one-line '<expr>'
#   scripts/hpj_oracle.sh --file Cases.hs   # a whole Main, run verbatim
#   scripts/hpj_oracle.sh --self-test       # check the toolchain first
#   scripts/hpj_oracle.sh --emit-template   # the generated Main, to stdout
#
# The expression is Haskell.  The script evaluates it with
# `Text.PrettyPrint.HughesPJ` in scope, and with `Prelude`'s `<>` hidden
# because HughesPJ exports its own `<>`.  To read the expression from stdin,
# pass `-` in its place.
#
# Widths.  `-w` sets lineLength and `-r` sets the ribbon width.  These are
# the same two numbers that `Doc::render_with(w, r)` takes.  The style's
# `ribbonsPerLine` is `w/r`.  The port states its constants the same way
# (`RIBBON = round(110/1.5) = 73`).  The defaults, 110/73, are HS's console
# width (`renderDoc` in `Main/Console.hs`).  They are therefore what a bare
# `Doc::render()` uses on the CLI path.  The interactive server renders at
# HughesPJ's own default of 100/67.  `pretty_hpj.rs` names both pairs.
#
# pretty_hpj.rs       this script
# ------------------- ------------------------------------------------------
# render_with(w, r)   -w w -r r                    (PageMode)
# render()            the defaults, 110/73         (CLI path)
# render(), server    -w 100 -r 67                 (after set_display_width)
# one_line_render()   --one-line                   (OneLineMode)
# render_at(..)       no equivalent in the public API.  It calls pretty's
#                     internal `get1` with a starting column, and HughesPJ
#                     does not export `get1`.  Derive the surrounding Doc
#                     instead.
#
# Env:
#   HPJ_GHC=<path>          the compiler to use.  A compiler that is set but
#                           unusable stops the script with an error.  The
#                           script never falls through silently to a
#                           different compiler.
#   HPJ_ALLOW_ANY_PRETTY=1  proceed when the resolved compiler's `pretty` is
#                           not 1.1.3.6.  This is off by default.  A document
#                           that a different layout engine renders is not an
#                           oracle byte.  It is a wrong answer that looks
#                           correct, and it would enter the tree as a pin.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# The shared helper file, which supplies the OOM prologue.  A consumer that
# cannot read the file exits 2.  It does not fall back to a private copy.
# See gate_common.sh.
[ -r "$SCRIPT_DIR/gate_common.sh" ] || {
    echo "cannot read $SCRIPT_DIR/gate_common.sh" >&2; exit 2; }
# shellcheck source=gate_common.sh
. "$SCRIPT_DIR/gate_common.sh"

# The version of pretty that the port reproduces.  `pretty_hpj.rs` cites this
# version by name throughout ("pretty-1.1.3.6 `Text.PrettyPrint.HughesPJ`").
# The layout of pretty changes between releases.  The version is therefore
# part of what makes an answer from this script an oracle byte.
WANT_PRETTY=1.1.3.6
# The GHC that ships that version here.  `./setup.sh testing` already installs
# this GHC to build the oracle, so no second toolchain is necessary.  The
# script tries it only after $HPJ_GHC and after a `ghc` on PATH.  An operator's
# own compiler therefore wins over this path.  This is the same last-resort
# order that `gate_common.sh` uses for the linuxbrew maude.
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
        # A compiler that is set but unusable is the failure that the maude
        # resolver exists to stop.  A fall-through to a different compiler
        # would answer from a pretty that the operator did not choose, and it
        # would say nothing about that.
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
# The function writes the program in three pieces.  The user's expression
# therefore never passes through shell expansion.  Haskell operators include
# `$$`, `$+$` and `<>`, and an unquoted heredoc would consume every one of
# them.
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

# render <workdir> -> compiles and runs the program, and writes its stdout
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
# Every case is one of the port's own committed assertions, derived again
# here.  The cases check the toolchain, not the layout.  If a case disagrees,
# then one of two things is true.  Either this script does not drive the
# pretty that the port reproduces, or the port has regressed.  Until you
# answer that question, do not commit anything derived in the session.  Run
# the self-test before you derive a pin that you intend to keep.
#
# The last case is the only one whose ribbon differs from its line length.
# It is here because of a probe.  The probe multiplied the generated style's
# ribbon by 4, and all five equal-width cases still matched.  Every value that
# this script passes into `theStyle` needs a case that changes when the value
# changes.
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
    # (nested_sep_disjunct_second_item_column) at width 50 and ribbon 33.
    expect 50 33 \
        'let opp d = text "(" <> d <> text ")"; fa a = sep [text "F.", sep [nest 1 (opp (text a)), text "=>", nest 1 (text "RHS")]]; dj l = sep [text ("Q" ++ l ++ "."), sep [nest 1 (opp (text "DANTE")), text "C", nest 1 (sep [opp (fa (replicate 32 (head "A"))) <> text " &", opp (fa (replicate 32 (head "B")))])]] in text "(" <> sep (punctuate (text " |") [opp (dj "x"), opp (dj "y")]) <> text ")"' \
        '"((Qx.\n   (DANTE)\n  C\n   (F.\n     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)\n    =>\n     RHS) &\n   (F.\n     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)\n    =>\n     RHS)) |\n (Qy.\n   (DANTE)\n  C\n   (F.\n     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)\n    =>\n     RHS) &\n   (F.\n     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)\n    =>\n     RHS)))"'

    echo "self-test: $SELFTEST_PASS matched, $SELFTEST_FAIL failed" \
         "(pretty-$HAVE_PRETTY via $GHC)"
    [ "$SELFTEST_FAIL" -eq 0 ] || return 1
    # A case list that became empty would print "0 matched, 0 failed" and exit
    # 0.  That is the one result that this check must never give.
    [ "$SELFTEST_PASS" -gt 0 ] || { echo "self-test compared nothing" >&2; return 1; }
}

# derive -> only the literal from the RUST line, for the self-test to compare
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
    # Whole-Main mode.  A derivation session with shared bindings and a dozen
    # cases is a Haskell file, not a shell argument.  The script runs the file
    # unchanged.  The widths above do not apply, because the file states its
    # own widths.
    [ -r "$FILE" ] || die "cannot read --file $FILE"
    cp "$FILE" "$WORK/Main.hs"
    run_program "$WORK" "$WORK/Main.hs"
    exit $?
fi

[ -n "$EXPR" ] || die "no expression (pass one, or \`-\` to read stdin, or --file)"
emit_main > "$WORK/Main.hs"
run_program "$WORK" "$WORK/Main.hs"
exit $?
