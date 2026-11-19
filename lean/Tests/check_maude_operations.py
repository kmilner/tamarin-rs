"""Replay the discriminating examples in MaudeOperations.lean against Maude."""
import re
import subprocess
import sys

MODULE = """set show command off .
set show timing off .
fmod MSG is
  sorts Pub TamNat Msg TOP .
  subsorts Pub TamNat < Msg < TOP .
  ops a b : -> Msg . op h : Msg -> Msg .
  op public : -> Pub . op one : -> TamNat .
  op tplus : TamNat TamNat -> TamNat [assoc comm] .
  op list : TOP -> TOP . op cons : TOP TOP -> TOP . op nil : -> TOP .
  eq h(a) = b [variant] .
endfm
"""


def reply(command):
    process = subprocess.run(
        [sys.argv[1], "-no-banner", "-no-advise"],
        input=MODULE + command + " .\nquit\n",
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


if __name__ == "__main__":
    main()
