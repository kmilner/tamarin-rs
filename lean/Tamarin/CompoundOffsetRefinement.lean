import Tamarin.CompoundOffset

namespace Tamarin
namespace FreshAnswer
variable {sig : Signature}

/-- Any family of complete ordinary unifiers may be serialized with one
independent permutation per answer, provided the same permutation renames all
of that answer's ranges, including the explicit identity bindings. -/
theorem reify_complete {ι : Type} (p : Problem sig) (avoid vs : List Variable)
    (indices : List ι) (raw : ι → Substitution sig) (π : ι → VariablePermutation)
    (inventory : ∀ v, v ∈ vs ↔ p.Occurs v) (hc : CompleteSet p (indices.map raw))
    (fresh : ∀ i ∈ indices, ∀ v ∈ vs, ∀ w, ((raw i).image v).Occurs w →
      ¬ p.Occurs ((π i).forward w) ∧ (π i).forward w ∉ avoid) :
    let answers := indices.map fun i => (encode vs (raw i)).decode (π i)
    (Outcome.complete answers).CorrectIn p avoid ∧
      ∀ σ ∈ answers, ∀ v ∈ vs, ∀ t, (σ.image v).Occurs t → ¬ p.Occurs t ∧ t ∉ avoid := by
  have pred : (fun v => v ∈ vs) = p.Occurs := funext (fun v => propext (inventory v))
  have closed (i) (hi : i ∈ indices) (v) (hv : v ∈ vs) (t)
      (ht : (((encode vs (raw i)).decode (π i)).image v).Occurs t) :
      ¬ p.Occurs t ∧ t ∉ avoid := by
    rw [decode_encode_image, ite_eq_left hv] at ht
    obtain ⟨w,hw,rfl⟩ := (Term.occurs_rename ((raw i).image v) (π i).forward t).mp ht
    exact fresh i hi v hv w hw
  constructor
  · constructor
    · constructor
      · intro σ hσ
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hσ
        exact p.solves_instance (hc.sound _ (List.mem_map_of_mem hi))
          (pred ▸ decode_instance vs (raw i) (π i))
      · intro ρ solves
        obtain ⟨a,ha,hs⟩ := hc.covers ρ solves
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
        exact ⟨_, List.mem_map_of_mem hi, Substitution.instanceOn_trans _ hs (pred ▸ encode_instance vs (raw i) (π i))⟩
    · intro σ hσ v hv
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hσ
      exact (decode_encode_image ..).trans (ite_eq_right (fun hm => hv ((inventory v).mp hm)))
    · intro σ hσ v hv t ht _
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hσ
      exact (closed i hi v ((inventory v).mpr hv) t ht).2
  · intro σ hσ
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hσ
    exact closed i hi

end FreshAnswer
namespace CompoundOffset
variable {sig : Signature}

/-- Renamings of the retained variables and the branch-local auxiliary slot
are request data. All variables below both offsets share the renaming. -/
structure Decoder (q : Query sig) (avoid : List Variable) where
  retained : List Variable
  inventory : ∀ v, v ∈ retained ↔ q.a.Occurs v ∨ q.b.Occurs v
  π : Bool → VariablePermutation
  renamed : ∀ s v, v ∈ retained → ¬ q.problem.Occurs ((π s).forward v) ∧ (π s).forward v ∉ avoid
  slot : UInt64 → Variable
  typed : ∀ id, (slot id).sort = sig.acSort q.f
  fresh : ∀ id, ¬ q.problem.Occurs (slot id) ∧ slot id ∉ avoid
  fixed : ∀ id, (π true).forward (slot id) = slot id

namespace Decoder
variable {q : Query sig} {avoid : List Variable} (d : Decoder q avoid)

def keys := [q.x,q.y] ++ d.retained

theorem mem_keys (v : Variable) : v ∈ d.keys ↔ q.problem.Occurs v := by
  simp [keys, d.inventory, q.occurs]

def decodeRow (term : UInt64 → Term sig) (row : Array UInt64) : Option (Term sig) :=
  match row.toList with
  | [a] => some ((d.π false).subst sig |>.apply (term a))
  | [a,w] => some (.ac q.f (.var (d.slot w)) (((d.π true).subst sig).apply (term a)))
  | _ => none

def decodeArm (term : UInt64 → Term sig) (arm : Array (Array UInt64)) : Option (List (Variable × Term sig)) := do
  let [l,r] := arm.toList | none
  let shared := l.size == 2
  return [(q.x, ← d.decodeRow term l), (q.y, ← d.decodeRow term r)] ++
    d.retained.map (fun v => (v, .var ((d.π shared).forward v)))

private theorem scope (w : UInt64) (s : Bool) (v : Variable) (hv : v ∈ d.keys) (t : Variable)
    (ht : ((q.answer (d.slot w) (d.typed w) s).image v).Occurs t) :
    ¬ q.problem.Occurs ((d.π s).forward t) ∧ (d.π s).forward t ∉ avoid := by
  have ambient (t) (ht : q.a.Occurs t ∨ q.b.Occurs t) :=
    d.renamed s t ((d.inventory t).mpr ht)
  have result (h : (s = true ∧ t = d.slot w) ∨ q.a.Occurs t ∨ q.b.Occurs t) :
      ¬ q.problem.Occurs ((d.π s).forward t) ∧ (d.π s).forward t ∉ avoid := by
    rcases h with ⟨rfl,rfl⟩ | h
    · rw [d.fixed]; exact d.fresh w
    · exact ambient _ h
  rcases (q.occurs _).mp ((d.mem_keys _).mp hv) with rfl | rfl | ha
  · rw [q.at_x] at ht; apply result
    cases s <;> simp [Query.image, Term.Occurs] at ht ⊢ <;> grind
  · rw [q.at_y] at ht; apply result
    cases s <;> simp [Query.image, Term.Occurs] at ht ⊢ <;> grind
  · rw [q.ambient _ _ _ ha] at ht
    exact ht ▸ ambient v ha

private theorem stored (w : UInt64) (s : Bool) :
    (FreshAnswer.encode d.keys ((FreshAnswer.encode d.keys (q.answer (d.slot w) (d.typed w) s)).decode (d.π s))).bindings =
    [(q.x, ((d.π s).subst sig).apply (q.image (d.slot w) s q.b)),
     (q.y, ((d.π s).subst sig).apply (q.image (d.slot w) s q.a))] ++
    d.retained.map (fun v => (v, .var ((d.π s).forward v))) := by
  let raw := q.answer (d.slot w) (d.typed w) s
  let σ := (FreshAnswer.encode d.keys raw).decode (d.π s)
  have atKey (v) (hv : v ∈ d.keys) :
      σ.image v = ((d.π s).subst sig).apply (raw.image v) :=
    (FreshAnswer.decode_encode_image ..).trans (ite_eq_left hv)
  change ((q.x :: q.y :: d.retained).map fun v => (v,σ.image v)) = _
  simp only [List.map_cons, List.cons_append, List.nil_append]
  rw [atKey q.x (by simp [keys]), atKey q.y (by simp [keys])]
  simp only [raw, q.at_x, q.at_y, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro v hv
  rw [atKey v (by simp [keys, hv]), q.ambient _ _ _ ((d.inventory v).mp hv)]
  rfl

end Decoder

theorem packet_correctIn {run : UInt64 → UInt64 → SharedOffset.Packet} (numeric : SharedOffset.PacketCorrect run)
    (q : Query sig) (avoid : List Variable) (d : Decoder q avoid)
    (a b : UInt64) (term : UInt64 → Term sig) (ha : term a = q.a) (hb : term b = q.b) :
    ∃ answers : List (Substitution sig),
      ((run a b).toList.map (d.decodeArm term)).Perm
        (answers.map fun σ => some (FreshAnswer.encode d.keys σ).bindings) ∧
      (Outcome.complete answers).CorrectIn q.problem avoid ∧
      ∀ σ ∈ answers, ∀ v ∈ d.keys, ∀ t, (σ.image v).Occurs t → ¬ q.problem.Occurs t ∧ t ∉ avoid := by
  have ne : a ≠ b := by
    intro he
    have eq := ha.symm.trans ((congrArg term he).trans hb)
    exact q.distinct Substitution.identity (eq ▸ EquivB.refl _)
  obtain ⟨w, hp⟩ := numeric a b ne
  let raw := q.answer (d.slot w) (d.typed w)
  let args := [false,true]
  let result := args.map fun s => (FreshAnswer.encode d.keys (raw s)).decode (d.π s)
  have hc : CompleteSet q.problem (args.map raw) := q.complete _ _ (d.fresh w).1
  have certified := FreshAnswer.reify_complete q.problem avoid d.keys args raw d.π d.mem_keys hc
    (fun s _ => d.scope w s)
  refine ⟨result, ?_, certified⟩
  have mapped := hp.map (d.decodeArm term)
  simpa [result, args, raw, Decoder.decodeArm, Decoder.decodeRow, d.stored, ha, hb, Query.image,
    Substitution.apply, Term.subst, VariablePermutation.subst, d.fixed] using mapped

end CompoundOffset
end Tamarin
