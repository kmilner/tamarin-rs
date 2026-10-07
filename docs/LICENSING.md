# Licensing notes

[Back to README](../README.md)

All contributions to this repository are considered MIT-licensed by default
(see [LICENSE](../LICENSE)). This does not replace the GPL 3.0 terms on code
derived from Tamarin. Preserve the existing license notices when contributing
to those files. The built binary remains GPL 3.0.

The `tamarin-prover/` submodule is a separate upstream project licensed under
GPL 3.0 (see [its license](../tamarin-prover/LICENSE)). The files under
`patches/` modify those GPL sources and are also GPL 3.0.

The licensing situation of this code is somewhat complicated. Portions of the
code are written based only on the observable output behaviour of tamarin-prover
while other parts were written with access to Tamarin's GPL 3.0 code. To my understanding,
this makes the resulting binary GPL 3.0 for the moment, as some of the contents are
a 'translation' of GPL 3 code.

Relicensing tamarin-prover is made difficult because of a very long tail of
contributors over many years, making it very difficult to get in touch with each
and every one of them to relicense their contributions. An eventual goal is to
relicense tamarin-rs fully under MIT if possible, which will require one or both of:

- Permission of the largest contributors (or their institutions, where the institution
  is the only party capable of relicensing).
- Where getting permission is infeasible, replacing the associated contribution with a
  cleanroom implementation of the feature.

Cleanroom implementations have to be performed by an LLM with access only to the observable
behaviour of tamarin-prover, not the source code. Unfortunately I (as a contributor to
tamarin-prover) am, to my understanding, tainted and cannot participate in this process
except to audit the output. Any work on this should be tracked along with full tool-call transcripts
to prove there was no access to GPL 3.0 source.
The segments being reimplemented have to be sufficiently broad
so as to not inherit any information about the GPL 3.0 source code beyond broad module interfaces
etc. Early experiments with clean room implementation of the formatting code had limited success,
so for now there is no active work on this.

Ported files carry an explicit GPL 3.0 notice at the top. These notices are
maintained independently of source references; editing or removing a reference
does not change a file's licensing designation.

Source comments refer to files and symbols in the pinned `tamarin-prover/`
submodule, for example `Theory/Model/Rule.hs#getRuleName`. Paths may use an
unambiguous suffix.

Currently no one has granted permission, because I haven't started asking yet. If you want to
preempt this and give your permission please send me an email or file a github issue!

These notes describe the project's licensing policy and plans, not legal advice.
