import Tamarin.MatchingSignatureExtension
import Tamarin.TotalUnifyPacket
import Tamarin.MaudeOperations

/-! The table packet declares all operators in the Tamarin module. Callers
can also choose arbitrary names, including names absent from the packet.
Run table commands in this full atom universe, and verify that the concrete
reply mentions only names the Rust dictionary can reconstruct. -/
namespace Tamarin.TableAmbient
open TotalUnifyWire SignatureExtension Rewriting

abbrev atoms : Signature where
  FreeSym := Empty
  CSym := Empty
  ACSym := Empty
  Atom := Nat × SortId
  arity := Empty.elim
  inputSort := fun f => nomatch f
  outputSort := Empty.elim
  cSort := Empty.elim
  acSort := Empty.elim
  atomSort := Prod.snd

abbrev sig (d : Dictionary) := joined d.sig atoms
variable {d : Dictionary}

def liftTerm (t : Term d.sig) : Term (sig d) := embed atoms t

def liftRules (rs : Problem d.sig) : Problem (sig d) := query atoms rs

def projectSubst (σ : Substitution (sig d)) : Substitution d.sig := restrictSubst σ

/-- The common substitution wire uses equation roots to enumerate all
observed variables. A variant tuple observes both occurrences identically. -/
def observations {s : Signature} (q : List (Term s)) : Problem s := q.map fun t => ⟨t,t⟩

theorem inventory {s : Signature} (q : List (Term s)) (v : Variable) :
    v ∈ (observations q).variables ↔ Observed q v := by
  rw [Problem.mem_variables]
  constructor
  · rintro ⟨e,he,h⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
    exact ⟨t,ht,h.elim id id⟩
  · rintro ⟨t,ht,h⟩
    exact ⟨_,List.mem_map_of_mem ht,Or.inl h⟩

private def known : Term (sig d) → Bool
  | .var _ => true
  | .atom (.inl _) => true
  | .atom (.inr _) => false
  | .free (.inl _) as => (List.ofFn fun i => known (as i)).all id
  | .free (.inr f) _ => nomatch f
  | .ac (.inl _) a b | .comm (.inl _) a b => known a && known b
  | .ac (.inr f) _ _ | .comm (.inr f) _ _ => nomatch f

private theorem known_iff (t : Term (sig d)) : known t = true ↔ Local t := by
  induction t with
  | var => exact ⟨fun _ => trivial,fun _ => rfl⟩
  | atom a => cases a <;> simp [known,Local]
  | free f as ih => cases f with
    | inl g => simpa [known,Local] using forall_congr' ih
    | inr g => exact nomatch g
  | ac f a b ih ik | comm f a b ih ik => cases f with
    | inl g => simpa [known,Local] using and_congr ih ik
    | inr g => exact nomatch g

private def imagesKnown (q : List (Term d.sig)) (rows : List (Variant (sig d))) :=
  rows.all fun a => (observations q).variables.all fun v => known (a.subst.image v)

def emit (q : List (Term d.sig)) (rows : List (Variant (sig d))) : Option (Array (Array UInt64)) :=
  if imagesKnown q rows then pack (observations q) (rows.map fun a => projectSubst a.subst)
  else none

def Decodes (q : List (Term d.sig)) (wire : Array (Array UInt64)) (rows : List (Variant (sig d))) : Prop :=
  Packet.Decodes (observations q) wire (rows.map fun a => projectSubst a.subst) ∧
    ∀ a ∈ rows, ∀ v, Observed q v → liftTerm ((projectSubst a.subst).image v) = a.subst.image v

theorem emit_correct {q : List (Term d.sig)} {rows wire} (h : emit q rows = some wire) : Decodes q wire rows := by
  unfold emit at h
  split at h
  next ok =>
    refine ⟨Packet.pack_decodes _ _ _ h,?_⟩
    intro a ha v hv
    have bounded := List.all_eq_true.mp (List.all_eq_true.mp ok a ha) v ((inventory q v).mpr hv)
    exact embed_restrict _ ((known_iff _).mp bounded)
  next => contradiction

end Tamarin.TableAmbient
