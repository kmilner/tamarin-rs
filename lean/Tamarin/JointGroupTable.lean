import Tamarin.XorTable
import Tamarin.MixedGroupPresentation

/-! Classify a single presentation containing two independently protected groups.
The complete table is available to each root proof, including the checks on
additional constructor equations. -/
namespace Tamarin.JointGroupTable
open Rewriting DHPeer ConstructorVariants
variable {sig : Signature}

private def extraHead [DecidableEq sig.FreeSym] (s : Symbols sig) (x : XorTable.Schema sig) (h : Head sig) : Bool :=
  ConstructorExtension.extraHead s h && x.extraHead h

def accepts [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]
    (s : Symbols sig) (keys : Fin 3 → Variable) (x : XorTable.Schema sig)
    (w : Head sig → Nat) (fuel : Nat) (rs : Problem sig) : Bool :=
  let more := rs.filter fun r => extraHead s x (head r.lhs)
  let joint := Schemas.rules s keys ++ x.rows more
  s.mul != x.f && TablePresentation.Agrees rs joint && SymbolWeight.decreasing w joint &&
    TableDecrease.sorted joint && more.all (ConstructorRows.checkedRow joint fuel)

section
variable {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    {x : XorTable.Schema sig} {more : Problem sig}

private def XRow (x : XorTable.Schema sig) (r : Equation sig) :=
  r = x.duplicate ∨ r = x.unit ∨ r = x.cancel

private theorem XRow.atHead {r : Equation sig} (h : XRow x r) : head r.lhs = .ac x.f := by
  rcases h with rfl | rfl | rfl <;> rfl

private theorem partition {r : Equation sig} (h : r ∈ (T.append (x.rows more)).rules) :
    r ∈ T.rules ∨ XRow x r ∨ r ∈ more := by
  change r ∈ T.rules ++ x.duplicate :: x.unit :: x.cancel :: more at h
  rcases List.mem_append.mp h with dh | rest
  · exact .inl dh
  · simp only [List.mem_cons] at rest
    rcases rest with d | u | c | tail
    · exact .inr (.inl (.inl d))
    · exact .inr (.inl (.inr (.inl u)))
    · exact .inr (.inl (.inr (.inr c)))
    · exact .inr (.inr tail)

private theorem dhTable [DecidableEq sig.FreeSym] (base : ExactTable E) (sep : s.mul ≠ x.f)
    (outside : ∀ r ∈ more, extraHead s x (head r.lhs)) : ProtectedTable (E.append (x.rows more)) where
  apps := by
    intro r hr
    rcases partition hr with dh | row | more
    · exact base.apps r dh
    · rcases row with rfl | rfl | rfl <;> trivial
    · have h := (Bool.and_eq_true_iff.mp (outside r more)).1
      cases e : r.lhs <;> simp_all [ConstructorExtension.extraHead,head,headModel,Model.eval,Application]
  atHead := by
    intro r hr hd
    rcases partition hr with dh | row | more
    · exact base r dh
    · rw [row.atHead] at hd
      rcases hd with h | h | h | h
      all_goals first | cases h | exact (sep (Head.ac.inj h.symm)).elim
    · have h := (Bool.and_eq_true_iff.mp (outside r more)).1
      rcases hd with e | e | e | e <;> simp [e,ConstructorExtension.extraHead] at h

private theorem xorBucket [DecidableEq sig.FreeSym] (base : ExactTable E) (sep : s.mul ≠ x.f)
    (outside : ∀ r ∈ more, extraHead s x (head r.lhs)) (r : Equation sig)
    (hr : r ∈ (T.append (x.rows more)).rules) (h : head r.lhs = .ac x.f) : XRow x r := by
  rcases partition hr with dh | row | more
  · rcases base.heads dh with e | e | e <;> rw [h] at e
    · exact (sep (Head.ac.inj e.symm)).elim
    · cases e
    · cases e
  · exact row
  · have ex := (Bool.and_eq_true_iff.mp (outside r more)).2; simp [h,XorTable.Schema.extraHead] at ex

/-- A nullary constant is distinct from both active free DH operators.
The additional group rows have AC heads. -/
private theorem inertConstant (base : ExactTable E) (g : sig.FreeSym) (arity : sig.arity g = 0)
    (outside : ∀ r ∈ more, head r.lhs ≠ .free g) :
    Head.free g ∉ ruleHeads (T.append (x.rows more)).rules := by
  rintro hh; obtain ⟨r,hr,e⟩ := List.mem_map.mp hh
  rcases partition hr with dh | row | more
  · rcases base.heads dh with h | h | h <;> rw [e] at h
    · cases h
    · have eq := congrArg sig.arity (Head.free.inj h); simp [s.invArity,arity] at eq
    · have eq := congrArg sig.arity (Head.free.inj h); simp [s.powArity,arity] at eq
  · have h := row.atHead; rw [e] at h; cases h
  · exact outside r more e

private theorem inactive [DecidableEq sig.FreeSym] (base : ExactTable E) (outside : ∀ r ∈ more, extraHead s x (head r.lhs))
    (f : sig.ACSym) (nd : f ≠ s.mul) (nx : f ≠ x.f) :
    Head.ac f ∉ ruleHeads (T.append (x.rows more)).rules := by
  rintro hh; obtain ⟨r,hr,e⟩ := List.mem_map.mp hh
  rcases partition hr with dh | row | more
  · rcases base.heads dh with h | h | h <;> rw [e] at h
    · exact nd (Head.ac.inj h)
    · cases h
    · cases h
  · exact nx (Head.ac.inj (e.symm.trans row.atHead))
  · have h := (Bool.and_eq_true_iff.mp (outside r more)).2; simp [e,XorTable.Schema.extraHead] at h

private theorem otherMember (base : ExactTable E) {r}
    (hr : r ∈ (T.append (x.rows more)).rules)
    (dh : ¬ChurchRosser.DHHead s (head r.lhs)) (xor : head r.lhs ≠ .ac x.f) : r ∈ more := by
  rcases partition hr with h | row | more
  · rcases base.heads h with h | h | h
    · exact (dh (.inr (.inr (.inr h)))).elim
    · exact (dh (.inr (.inl h))).elim
    · exact (dh (.inl h)).elim
  · exact (xor row.atHead).elim
  · exact more

end
variable [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]

theorem accepts_sound (s : Symbols sig) (keys : Fin 3 → Variable) (x : XorTable.Schema sig)
    (typed : ∀ i, (keys i).sort = .msg) (distinct : ∀ i j, keys i = keys j → i = j)
    {w fuel rs} (ok : accepts s keys x w fuel rs) :
    ReferenceReduction.Bound rs ∧ MaudeOperations.CanonicalPresentation (ruleRoot rs) ∧
      MaudeOperations.FiniteVariantProperty (ruleRoot rs) := by
  let more := rs.filter fun r => extraHead s x (head r.lhs)
  have out : ∀ r ∈ more, extraHead s x (head r.lhs) := fun _ h => (List.mem_filter.mp h).2
  let E := Schemas.E s keys typed distinct
  let base := Schemas.exactTable s keys typed distinct
  let joint := (Schemas.T s keys typed distinct).append (x.rows more)
  obtain ⟨⟨⟨⟨sep,agrees⟩,wok⟩,sorted⟩,checked⟩ := by simpa only [accepts,Bool.and_eq_true,bne_iff_ne] using ok
  have dh := dhTable base sep out
  have bucket := xorBucket base sep out
  have zero : Head.free x.z ∉ ruleHeads joint.rules := inertConstant base x.z x.zeroArity (by
    intro r hr h; have ex := (Bool.and_eq_true_iff.mp (out r hr)).2; simp [h,XorTable.Schema.extraHead] at ex)
  let X := x.onTable joint.rules (List.mem_append_right _ List.mem_cons_self)
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)) bucket dh.apps zero
  have neutral : Head.free s.neutral ∉ ruleHeads joint.rules := inertConstant base s.neutral s.neutralArity (by
    intro r hr h; have ex := (Bool.and_eq_true_iff.mp (out r hr)).1; simp [h,ConstructorExtension.extraHead] at ex)
  have scope : ReferenceReduction.Bound joint.rules := SymbolWeight.bound wok
  apply MixedGroupPresentation.Evidence.sound (E := E.append (x.rows more)) (X := X)
  refine ⟨rfl,agrees,⟨dh.apps,SymbolWeight.terminating wok,TableDecrease.sortPreserving sorted⟩,scope,dh,
    constructor_node_normal _ dh.apps _ neutral (fun i => Fin.elim0 (s.neutralArity ▸ i)),
    (fun r hr h => x.typedOfActive (bucket r hr h)),inactive base out,?_⟩
  intro r hr notDH notXor
  have mem := otherMember base hr notDH (x := x) notXor
  exact ConstructorRows.checkedRow_sound hr scope dh.apps (List.all_eq_true.mp checked r mem)

end Tamarin.JointGroupTable
