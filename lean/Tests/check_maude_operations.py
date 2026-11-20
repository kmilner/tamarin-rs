"""Replay the discriminating examples in MaudeOperations.lean against Maude."""
import re
import subprocess
import sys

MODULE = """set show command off .
set show timing off .
fmod MSG is
  sorts Pub TamNat Msg TOP .
  subsorts Pub TamNat < Msg < TOP .
  ops a b c : -> Msg . ops h f g : Msg -> Msg .
  ops plus times : Msg Msg -> Msg [assoc comm] .
  op public : -> Pub . op one : -> TamNat .
  op tplus : TamNat TamNat -> TamNat [assoc comm] .
  op list : TOP -> TOP . op cons : TOP TOP -> TOP . op nil : -> TOP .
  eq h(a) = b [variant] .
  eq plus(f(Z:Msg),a) = g(Z:Msg) [variant] .
endfm
"""


def reply(command, module=MODULE):
    process = subprocess.run(
        [sys.argv[1], "-no-banner", "-no-advise"],
        input=module + command + " .\nquit\n",
        capture_output=True, text=True, check=True, timeout=10,
    )
    if process.stderr.strip():
        raise AssertionError(process.stderr)
    return process.stdout


def check(command, observation):
    output = reply(command)
    assert observation in output, (command, output)


def main():
    check("match in MSG : b <=? h(a)", "No match.")
    check("match in MSG : X:Msg <=? h(X:Msg)", "X:Msg --> h(X:Msg)")
    check("reduce in MSG : h(a)", "result Msg: b")
    ill = "tplus(public,one)"
    swapped = "tplus(one,public)"
    check(f"match in MSG : {ill} <=? {swapped}", "empty substitution")
    check(f"match in MSG : X:Msg <=? {ill}", "No match.")
    check(f"unify in MSG : {ill} =? {swapped}", "empty substitution")

    # TOP is the sort of the administrative wrapper. No input variable
    # declared by Tamarin can capture it. Its free cons/nil spine fixes width.
    for l, r in [("X:Msg", "list(nil)"), ("list(cons(X:Msg,nil))", "list(nil)"),
                 ("list(cons(list(nil),nil))", "list(cons(X:Msg,nil))")]:
        check(f"unify in MSG : {l} =? {r}", "No unifier.")
        check(f"match in MSG : {l} <=? {r}", "No match.")

    # A repeated capture must agree across both AC operators.
    output = reply("match in MSG : list(cons(plus(X:Msg,Y:Msg),cons(times(X:Msg,a),nil)))"
                   " <=? list(cons(plus(b,a,c),cons(times(a,plus(c,a)),nil)))")
    assert len(re.findall(r"^Matcher ", output, re.MULTILINE)) == 1, output
    assert "Y:Msg --> b" in output and re.search(r"X:Msg --> plus\((?:a, c|c, a)\)", output), output
    # The selected factors need not be siblings in the original syntax.
    output = reply("reduce in MSG : plus(f(c),plus(b,a))")
    assert re.search(r"result Msg: plus\((?:b, g\(c\)|g\(c\), b)\)", output), output

    # Variant narrowing in Core Maude requires explicit AC coherence. Reduction
    # already uses extension. The open row alone cannot cover the X = a case.
    query = "get variants in MSG : plus(f(c),b,X:Msg)"
    bare = reply(query)
    assert "No more variants." in bare and len(re.findall(r"^Variant ", bare, re.MULTILINE)) == 1, bare
    assert re.search(r"^X:Msg --> [#%]\d+:Msg$", bare, re.MULTILINE), bare
    completion = "  eq plus(f(Z:Msg),a,R:Msg) = plus(g(Z:Msg),R:Msg) [variant] ."
    extended = reply(query, MODULE.replace("endfm", completion + "\nendfm"))
    assert "No more variants." in extended, extended
    assert re.search(r"^Msg: plus\((?:b, g\(c\)|g\(c\), b)\)\nX:Msg --> a$", extended, re.MULTILINE), extended
    assert re.search(r"^X:Msg --> plus\((?:a, ([#%]\d+:Msg)|([#%]\d+:Msg), a)\)$", extended, re.MULTILINE), extended

    output = reply("get variants in MSG : list(cons(h(X:Msg),cons(X:Msg,nil)))")
    assert "No more variants." in output, output
    rows = re.findall(r"^TOP: (.+)\nX:Msg --> (.+)$", output, re.MULTILINE)
    assert len(rows) == len(re.findall(r"^Variant \d+$", output, re.MULTILINE)), output
    observations = set()
    for value, binding in rows:
        if binding == "a":
            assert value == "list(cons(b, cons(a, nil)))", value
            observations.add("specialized")
        else:
            assert re.fullmatch(r"[#%]\d+:Msg", binding), binding
            assert value == f"list(cons(h({binding}), cons({binding}, nil)))", value
            observations.add("open")
    assert observations == {"open", "specialized"}, output

    # Limit the request explicitly. The combined table has infinitely many
    # incomparable variants, proved in Tests/VariantCompositionLimit.lean.
    chain = """fmod CHAIN is
      sort T .
      ops f g s : T -> T .
      eq f(s(X:T)) = g(X:T) [variant] .
      eq g(X:T) = f(X:T) [variant] .
    endfm
    """
    out = reply("get variants [6] in CHAIN : f(X:T)", chain)
    bindings = re.findall(r"^X:T --> (.*)$", out, re.MULTILINE)
    assert len(bindings) == 6, out
    for depth, binding in enumerate(bindings):
        witness = re.search(r"[#%]\d+:T", binding)
        assert witness and binding == "s(" * depth + witness.group() + ")" * depth, out


if __name__ == "__main__":
    main()
