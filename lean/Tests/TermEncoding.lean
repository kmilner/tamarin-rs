import Tamarin.SignatureTable
import Tamarin.ACRepresentation

namespace Tamarin.TermEncodingChecks

/-- A finite, inhabited codec with mixed arities and sorts. No assumed
round-trip oracle is needed to construct the encoding witness. -/
private def sig : Signature where
  FreeSym := Fin 2
  CSym := Fin 1
  ACSym := Fin 2
  Atom := Fin 5
  arity := fun f => if f.val = 0 then 2 else 0
  inputSort := fun _ i => if i.val = 0 then .nat else .msg
  outputSort := fun f => if f.val = 0 then .msg else .nat
  cSort := fun _ => .msg
  acSort := fun f => if f.val = 0 then .msg else .nat
  atomSort := fun a => match a.val with
    | 0 => .pub | 1 => .fresh | 2 => .msg | 3 => .node | _ => .nat

private instance : DecidableEq sig.ACSym := inferInstanceAs (DecidableEq (Fin 2))

private def codec : SignatureEncoding sig :=
  ⟨SignatureTable.indexEncoding 2, SignatureTable.indexEncoding 1,
    SignatureTable.indexEncoding 2, SignatureTable.indexEncoding 5⟩

private def pair (a b : NumericTerm) : NumericTerm :=
  .free 0 2 (Fin.cases a (fun _ => b))

-- Unknown IDs are rejected separately in each namespace.
example : TermEncoding.decode codec (.atom 5) = none := rfl
example : TermEncoding.decode codec (.free 2 0 Fin.elim0) = none := rfl
example : TermEncoding.decode codec (.comm 1 (.atom 0) (.atom 1)) = none := rfl
example : TermEncoding.decode codec (.ac 2 (.atom 0) (.atom 1)) = none := rfl
example : TermEncoding.decode codec (pair (.atom 4) (.atom 5)) = none := rfl

-- Wrong free arities are rejected, including an apparently nullary application.
example : TermEncoding.decode codec (.free 0 0 Fin.elim0) = none := rfl
example : TermEncoding.decode codec (.free 1 1 (fun _ => .atom 4)) = none := rfl

-- Both zero-arity functions and mixed-sort compound terms can be admitted.
example : TermEncoding.decodeChecked codec .nat (.free 1 0 Fin.elim0) =
    some (.free ⟨1, by decide⟩ Fin.elim0) := rfl
example : (TermEncoding.decodeChecked codec .msg (pair (.atom 4) (.atom 0))).isSome =
    true := rfl

example : (TermEncoding.decodeChecked codec .msg (.comm 0 (.atom 0) (.atom 1))).isSome =
    true := rfl

-- A correctly declared result sort does not hide an ill-sorted child.
example : TermEncoding.decodeChecked codec .msg (pair (.atom 0) (.atom 4)) = none := rfl
example : TermEncoding.decodeChecked codec .msg (pair (.atom 4) (.atom 3)) = none := rfl
example : TermEncoding.decodeChecked codec .msg (.comm 0 (.atom 0) (.atom 3)) = none := rfl
example : TermEncoding.decodeChecked codec .nat (.ac 1 (.atom 4) (.atom 0)) = none := rfl
example : TermEncoding.decodeChecked codec .msg (.var 9 .node) = none := rfl
example : TermEncoding.decodeChecked codec .nat (.var 9 .msg) = none := rfl
example : TermEncoding.decodeChecked codec .msg (.var 9 .nat) =
    some (.var ⟨9, .nat⟩) := rfl

-- Full variable identity includes sort; neither equal IDs nor equal namespace
-- indices identify different terms. The generic theorem covers arbitrary trees.
example : TermEncoding.decode codec (.var 9 .pub) = some (.var ⟨9, .pub⟩) := rfl
example : TermEncoding.decode codec (.var 9 .fresh) = some (.var ⟨9, .fresh⟩) := rfl
example (t : Term sig) : TermEncoding.decode codec (TermEncoding.encode codec t) = some t :=
  TermEncoding.decode_encode codec t

-- AC arrays admit arbitrary entries and preserve multiplicity; they have no unit.
example (f : sig.ACSym) : ACRepresentation.decode f [] = none := rfl
example (f : sig.ACSym) (a : Term sig) : ACRepresentation.decode f [a] = some a := rfl
example (f : sig.ACSym) (a : Term sig) :
    ACRepresentation.decode f [a, a] = some (.ac f a a) := rfl
example (f : sig.ACSym) (a b c : Term sig) :
    EquivB (ACRepresentation.fold f a [b, c]) (ACRepresentation.fold f c [a, b]) :=
  ACRepresentation.decode_perm f ((List.Perm.cons a (List.Perm.swap c b [])).trans (List.Perm.swap c a [b])) _ _ rfl rfl

-- Nested occurrences of other AC symbols must not be flattened into this one.
example (a b c : Term sig) :
    ACRepresentation.flatten (⟨0, by decide⟩ : sig.ACSym)
      (Term.ac (sig := sig) ⟨0, by decide⟩ a (.ac ⟨1, by decide⟩ b c)) =
      ACRepresentation.flatten (⟨0, by decide⟩ : sig.ACSym) a ++ [.ac ⟨1, by decide⟩ b c] := by
  simp [ACRepresentation.flatten, sig]

end Tamarin.TermEncodingChecks
