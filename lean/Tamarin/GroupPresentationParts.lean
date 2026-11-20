import Tamarin.PresentationComponents
import Tamarin.XorPresentation
import Tamarin.DHConstructorExtension

/-! The DH and exponent-two group certificates, projected onto an arbitrary
common presentation. Their local proofs also apply when more operators have rules. -/
namespace Tamarin.GroupPresentationParts
open Rewriting DHPeer ConstructorVariants PresentationComponents
variable {sig : Signature}
variable [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]

private def owns (hs : List (Head sig)) (h : Head sig) := hs.any fun g => ConstructorRows.headEq h g

private theorem owns_iff (hs : List (Head sig)) (h : Head sig) : owns hs h ↔ h ∈ hs := by
  simp [owns,ConstructorRows.headEq_iff]

def dhPart (s : Symbols sig) (ks : Fin 3 → Variable) : Part sig :=
  ⟨owns [.free s.pow,.free s.inv,.free s.one,.ac s.mul,.free s.neutral],Schemas.rules s ks⟩

def xorPart (x : XorTable.Schema sig) : Part sig := ⟨owns [.ac x.f,.free x.z],x.rows []⟩

variable {s : Symbols sig} {ks : Fin 3 → Variable} {rs : Problem sig}

private theorem dhOwns {h : Head sig} : (dhPart s ks).owns h ↔ ChurchRosser.DHHead s h ∨ h = .free s.neutral := by
  simp only [dhPart,owns_iff,List.mem_cons,List.not_mem_nil,or_false,ChurchRosser.DHHead]
  grind

def dhTable (inc : Inventory (dhPart s ks) rs) (typed : ∀ i, (ks i).sort = .msg)
    (inj : ∀ i j, ks i = ks j → i = j) : Table s where
  rules := rs
  actual _ := ks
  actualSort _ := typed
  distinct _ := inj
  present r := inc.present _ ((Schemas.T s ks typed inj).present r)

def dhExtra (inc : Inventory (dhPart s ks) rs) (typed : ∀ i, (ks i).sort = .msg)
    (inj : ∀ i j, ks i = ks j → i = j) : ExtraTable (dhTable inc typed inj) where
  actual _ := ks
  sorted _ := typed
  distinct _ := inj
  present r := inc.present _ ((Schemas.E s ks typed inj).present r)

theorem protectedDH (inc : Inventory (dhPart s ks) rs) (typed : ∀ i, (ks i).sort = .msg)
    (inj : ∀ i j, ks i = ks j → i = j) (apps : ∀ r ∈ rs, Application r.lhs) :
    ProtectedTable (dhExtra inc typed inj) :=
  ⟨apps,fun r hr hd => Schemas.exactTable s ks typed inj r (inc.only r hr (dhOwns.mpr (.inl hd)))⟩

theorem dhLocal (inc : Inventory (dhPart s ks) rs) (typed : ∀ i, (ks i).sort = .msg)
    (inj : ∀ i j, ks i = ks j → i = j) (apps : ∀ r ∈ rs, Application r.lhs)
    (h : Head sig) (used : h ∈ ruleHeads rs) (owned : (dhPart s ks).owns h) : Local rs h := by
  let dh := protectedDH inc typed inj apps
  have base := Schemas.exactTable s ks typed inj
  have unused (f : sig.FreeSym) (arity : sig.arity f = 0) (own : (dhPart s ks).owns (.free f)) :
      Head.free f ∉ ruleHeads rs := by
    rintro mem
    obtain ⟨r,hr,eq⟩ := List.mem_map.mp mem
    rcases base.heads (inc.only r hr (eq ▸ own)) with m|i|p
    · rw [eq] at m; cases m
    · have a := congrArg sig.arity (Head.free.inj (eq.symm.trans i)); simp [arity,s.invArity] at a
    · have a := congrArg sig.arity (Head.free.inj (eq.symm.trans p)); simp [arity,s.powArity] at a
  have neutral : Normal (ruleRoot rs) s.neutralTerm :=
    constructor_node_normal _ apps _ (unused s.neutral s.neutralArity (dhOwns.mpr (.inr rfl)))
      (fun i => Fin.elim0 (s.neutralArity ▸ i))
  rcases dhOwns.mp owned with (rfl | rfl | rfl | rfl) | rfl
  · exact ⟨fun r hr hd => ChurchRosser.protected_unique dh neutral r hr (.inl hd),
      free_head_paths dh.inventory dh.product dh.inverse dh.unit dh.power _ (.inl rfl)⟩
  · exact ⟨fun r hr hd => ChurchRosser.protected_unique dh neutral r hr (.inr (.inl hd)),
      free_head_paths dh.inventory dh.product dh.inverse dh.unit dh.power _ (.inr rfl)⟩
  · exact (unused _ s.oneArity owned used).elim
  · exact ⟨⟨ChurchRosser.protectedProduct dh,
      fun r hr hd => ChurchRosser.protected_unique dh neutral r hr (.inr (.inr (.inr hd))),
      kind_product_paths dh.inventory dh.product dh.inverse dh.unit⟩⟩
  · exact (unused _ s.neutralArity owned used).elim

theorem xorLocal (x : XorTable.Schema sig) (inc : Inventory (xorPart x) rs)
    (apps : ∀ r ∈ rs, Application r.lhs) (h : Head sig) (used : h ∈ ruleHeads rs)
    (owned : (xorPart x).owns h) : Local rs h := by
  have own (g : Head sig) : (xorPart x).owns g ↔ g = .ac x.f ∨ g = .free x.z := by
    simp [xorPart,owns_iff]
  have rows {r} (hr : r ∈ rs) (hit : (xorPart x).owns (head r.lhs)) :
      r = x.duplicate ∨ r = x.unit ∨ r = x.cancel := by
    simpa [xorPart,XorTable.Schema.rows] using inc.only r hr hit
  have unit : Head.free x.z ∉ ruleHeads rs := by
    rintro mem
    obtain ⟨r,hr,hd⟩ := List.mem_map.mp mem
    rcases rows hr ((own _).mpr (.inr hd)) with rfl|rfl|rfl <;> cases hd
  rcases (own h).mp owned with rfl | rfl
  · let active := fun r (hr : r ∈ rs) (hd : head r.lhs = .ac x.f) => rows hr ((own _).mpr (.inl hd))
    let X := x.onTable rs (inc.present _ List.mem_cons_self)
      (inc.present _ (List.mem_cons_of_mem _ List.mem_cons_self)) active apps unit
    have ty r (hr : r ∈ rs) (hd : head r.lhs = .ac x.f) := x.typedOfActive (active r hr hd)
    exact ⟨⟨BinaryXor.product X ty,fun r hr hd => BinaryXor.uniqueRow X r hr hd (ty r hr hd),
      ⟨2,BinaryXor.kind_paths X (BinaryXor.redex_typed X ty)⟩⟩⟩
  · exact (unit used).elim

end Tamarin.GroupPresentationParts
