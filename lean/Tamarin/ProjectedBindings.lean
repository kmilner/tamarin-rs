import Tamarin.GraphUnification
import Tamarin.OrdinalAllocation
import Tamarin.AnswerProjection

/-! Interpretation of projected witness packets as finite keyed substitutions. -/
namespace Tamarin.ProjectedBindings
open ACSystem Homogeneous FactoredAC
variable {sig : Signature}

/-- A caller-side AC constructor may permute factors while building its term. -/
structure Order where
  arrange : List Variable → List Variable
  perm : ∀ xs, (arrange xs).Perm xs

def Order.identity : Order := ⟨id, List.Perm.refl⟩

/-- The first word selects the input variable. All remaining words select
allocated witnesses and constitute one nonempty AC image. -/
def readRow {n : Nat} (keys : Fin n → Variable) (f : sig.ACSym)
    (name : UInt64 → Variable) (order : Order) (row : Array UInt64) :
    Option (Variable × Term sig) := do
  let tag :: rest := row.toList | none
  let key ← (List.ofFn keys)[tag.toNat]?
  let image ← ACRepresentation.decode f ((order.arrange (rest.map name)).map Term.var)
  return (key, image)

def readArm {n : Nat} (keys : Fin n → Variable) (f : sig.ACSym)
    (name : UInt64 → Variable) (order : Order) (a : Arm) :=
  a.toList.mapM (readRow keys f name order)

/-- The decoded term is well-sorted and denotes exactly the original factors,
including repeated occurrences of a shared witness. -/
theorem decode_order (f : sig.ACSym) (o : Order) (x : Variable) (xs : List Variable)
    (sorts : ∀ v ∈ x :: xs, v.sort = sig.acSort f) :
    ∃ t, ACRepresentation.decode f ((o.arrange (x :: xs)).map Term.var) = some t ∧
      HasSort t (sig.acSort f) ∧ EquivB t ((Side.mk x xs).term f) := by
  have hp := o.perm (x :: xs)
  cases hr : o.arrange (x :: xs) with
  | nil => rw [hr] at hp; simp at hp
  | cons a rest =>
    rw [hr] at hp
    refine ⟨_, rfl, ACRepresentation.fold_hasSort _ _ _ ?_ ?_, ?_⟩
    · rw [← sorts a (hp.mem_iff.mp List.mem_cons_self)]
      exact .var _
    · intro t ht
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
      rw [← sorts v (hp.mem_iff.mp (List.mem_cons_of_mem a hv))]
      exact .var _
    · exact ACRepresentation.decode_perm f (hp.map Term.var) _ _ rfl rfl

private theorem mapM_map {α β γ : Type} (items : List α) (read : β → Option γ)
    (src : α → β) (dst : α → γ) (h : ∀ i, read (src i) = some (dst i)) :
    (items.map src).mapM read = some (items.map dst) := by
  induction items with
  | nil => rfl
  | cons i is ih => simp [h, ih]

private theorem mapM_ofFn {α β : Type} {n : Nat} (src : Fin n → α) (dst : Fin n → β)
    (read : α → Option β) (h : ∀ i, read (src i) = some (dst i)) :
    (List.ofFn src).mapM read = some (List.ofFn dst) := by
  simpa [List.finRange, List.map_ofFn, Function.comp_def] using mapM_map (List.finRange n) read src dst h

private theorem read_column {n : UInt64} (keys : Fin n.toNat → Variable) (f : sig.ACSym)
    (name : UInt64 → Variable) (order : Order) (rank : UInt64 → UInt64)
    (i : Fin n.toNat) (raw : Array UInt64) (x xs)
    (decoded : raw.toList.map (fun j => name (rank j)) = x :: xs)
    (sorts : ∀ j ∈ raw.toList, (name (rank j)).sort = sig.acSort f) :
    ∃ t, readRow keys f name order (#[i.val.toUInt64] ++ raw.map rank) = some (keys i, t) ∧
      HasSort t (sig.acSort f) ∧ EquivB t ((Side.mk x xs).term f) := by
  have kept (v) (hv : v ∈ x :: xs) : v.sort = sig.acSort f := by
    rw [← decoded] at hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    exact sorts j hj
  obtain ⟨t, ht, hs, he⟩ := decode_order f order x xs kept
  have word : i.val.toUInt64.toNat = i.val := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt n.toNat_lt_size)
  refine ⟨t, ?_, hs, he⟩
  simp [readRow, Array.toList_map, List.map_map, Function.comp_def, word, decoded, ht, i.isLt]

private theorem materializes {n : UInt64} {f : sig.ACSym} {rows} (fr : Frame f rows n.toNat)
    (name : UInt64 → Variable) (order : Order) (rank : UInt64 → UInt64)
    (a : Arm) (σ : Substitution sig) (rep : Represents fr (fun j => name (rank j)) a σ)
    (domain : DomainRestricted (problem f rows) σ)
    (typed : ∀ row ∈ a.toList, ∀ j ∈ row.toList, (name (rank j)).sort = sig.acSort f) :
    ∃ b : FreshAnswer sig, readArm fr.names f name order (AnswerProjection.tagArm rank a) = some b.bindings ∧
      ∀ v, EquivB ((FactoredAnswer.readBindings b).image v) (σ.image v) := by
  let src (i : Fin a.size) := #[i.val.toUInt64] ++ a[i].map rank
  let idx (i : Fin a.size) : Fin n.toNat := i.cast rep.1
  have each (i : Fin a.size) : ∃ t, readRow fr.names f name order (src i) = some (fr.names (idx i),t) ∧
      HasSort t (fr.names (idx i)).sort ∧ EquivB t (σ.image (fr.names (idx i))) := by
    obtain ⟨x, xs, dec, im⟩ := rep.2 (idx i)
    have dec' : a[i].toList.map (fun j => name (rank j)) = x :: xs := by
      simpa [idx, Array.getElem?_eq_getElem i.isLt] using dec
    obtain ⟨t, ht, hs, he⟩ := read_column fr.names f name order rank (idx i) a[i] x xs dec' (typed _ (by simp))
    exact ⟨t, ht, fr.sorts (idx i) ▸ hs, im ▸ he⟩
  let term (i : Fin a.size) := (each i).choose
  let entry (i : Fin a.size) := (fr.names (idx i), term i)
  let entries := List.ofFn entry
  have same {i j : Fin a.size} (e : fr.names (idx i) = fr.names (idx j)) : i = j :=
    Fin.ext (congrArg (fun k : Fin n.toNat => k.val) (fr.injective e))
  let packet : FreshAnswer sig := {
    bindings := entries
    sorted := by
      intro v t hm
      obtain ⟨i, he⟩ := List.mem_ofFn.mp hm
      cases he
      exact (each i).choose_spec.2.1
    consistent := by
      intro v t u ht hu
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp ht
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hu
      have hij := same ((congrArg Prod.fst hi).trans (congrArg Prod.fst hj).symm)
      cases hij
      exact (congrArg Prod.snd hi).symm.trans (congrArg Prod.snd hj) }
  refine ⟨packet, ?_, ?_⟩
  · simpa only [readArm, AnswerProjection.tagArm, Array.toList_ofFn] using
      mapM_ofFn src entry (readRow fr.names f name order) (fun i => (each i).choose_spec.1)
  · intro v
    change EquivB (Substitution.lookupBinding entries v) _
    by_cases hv : (problem f rows).Occurs v
    · obtain ⟨k, rfl⟩ := fr.live v ((occurs_iff_mem f rows v).mp hv)
      let i := k.cast rep.1.symm
      have hm : (fr.names k, term i) ∈ entries := List.mem_ofFn.mpr ⟨i,rfl⟩
      rw [Substitution.lookupBinding_eq_of_mem _ packet.consistent _ _ hm]
      exact (each i).choose_spec.2.2
    · rw [domain v hv, Substitution.lookupBinding_outside]
      · exact .refl _
      · intro hm
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
        exact hv (he ▸ (occurs_iff_mem f rows _).mpr (fr.used (idx i)))

/-- Only image words are witness ordinals; the first word of each row is a column. -/
def ordinals (out : Answers) := out.toList.flatMap fun a => a.toList.flatMap fun row => row.toList.tail

private theorem ordinal_bound {project n raw out} (h : AnswerProjection.Correct project)
    (projected : project n raw = some out) :
    ∀ j ∈ ordinals out, j.toNat < (AnswerProjection.keys raw).length := by
  obtain ⟨ok, rfl⟩ := (h _ _ _).mp projected
  intro j used
  obtain ⟨arm, ha, hm⟩ := List.mem_flatMap.mp used
  obtain ⟨row, hr, hj⟩ := List.mem_flatMap.mp hm
  simp only [Array.toList_map, List.mem_map] at ha
  obtain ⟨a, ha, rfl⟩ := ha
  simp only [AnswerProjection.tagArm, Array.toList_ofFn, List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨slot, hs, rfl⟩ : ∃ k ∈ a[i].toList, AnswerProjection.rank raw k = j :=
    by simpa using hj
  apply AnswerProjection.rank_lt ok
  exact List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨a[i], by simp, hs⟩⟩

/-- Interpret first-use ordinals with the caller's ascending allocator. Only the
finite occupied scope and the caller's embedding of variable identities matter. -/
theorem allocated_names {project n raw out} (projection : AnswerProjection.Correct project)
    (projected : project n raw = some out) (reserved : UInt64 → Bool) {ws}
    (alloc : OrdinalAllocation.allocate reserved (AnswerProjection.keys raw).length = some ws)
    (make : UInt64 → Variable) (injective : Function.Injective make) (s : SortId)
    (typed : ∀ i, (make i).sort = s) (avoid : List Variable)
    (occupied : ∀ i, make i ∈ avoid → reserved i = true) :
    let name := OrdinalAllocation.nameAt make ws
    (∀ i ∈ ordinals out, ∀ j ∈ ordinals out, name i = name j → i = j) ∧
    (∀ j ∈ ordinals out, (name j).sort = s) ∧ (∀ j ∈ ordinals out, name j ∉ avoid) :=
  OrdinalAllocation.names_correct alloc make s avoid (fun _ _ _ _ eq => injective eq)
    (fun j _ => typed j) occupied (ordinals out) (ordinal_bound projection projected)

theorem live_rank {out : Answers} {rank : UInt64 → UInt64} {j : UInt64}
    (used : j ∈ slots out) : rank j ∈ ordinals (out.map (AnswerProjection.tagArm rank)) := by
  obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp used
  obtain ⟨row, hr, hj⟩ := List.mem_flatMap.mp h
  have hm : AnswerProjection.tagArm rank a ∈ (out.map (AnswerProjection.tagArm rank)).toList := by
    simpa only [Array.toList_map] using List.mem_map_of_mem (f := AnswerProjection.tagArm rank) ha
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr hr)
  subst row
  refine List.mem_flatMap.mpr ⟨_,hm,List.mem_flatMap.mpr ?_⟩
  refine ⟨#[i.toUInt64] ++ a[i].map rank, ?_, ?_⟩
  · simp only [AnswerProjection.tagArm, Array.toList_ofFn, List.mem_ofFn]
    exact ⟨⟨i, hi⟩, rfl⟩
  · simpa using List.mem_map_of_mem (f := rank) hj

/-- Every projected arm is decoded, in order, to a concrete finite table.
Composition interprets its entries as a simultaneous substitution. -/
def Denotes {f : sig.ACSym} {rows n} (r : Request sig) (θ : Substitution sig)
    (fr : Frame f rows n) (name : UInt64 → Variable) (order : Order) (out : Answers) : Prop :=
  ∃ packets : List (FreshAnswer sig),
    out.toList.mapM (readArm fr.names f name order) = some (packets.map FreshAnswer.bindings) ∧
    CompleteSet r.problem (packets.map fun b => (FactoredAnswer.readBindings b).compose θ) ∧
    (Outcome.complete (packets.map fun b =>
      FreshAnswer.freshen r.problem r.avoid ((FactoredAnswer.readBindings b).compose θ))).CorrectIn
      r.problem r.avoid

private theorem instance_of_equiv {α β : Substitution sig}
    (equiv : ∀ v, EquivB (α.image v) (β.image v)) (seen : Variable → Prop) :
    Substitution.InstanceOn seen α β := by
  refine ⟨.identity, fun v _ => ?_⟩
  change EquivB _ (Substitution.identity.apply _)
  rw [Substitution.apply_identity]
  exact equiv v

private theorem lifts {n : UInt64} {f : sig.ACSym} {rows} (fr : Frame f rows n.toNat)
    {r : Request sig} {θ : Substitution sig} {out : Answers}
    (name : UInt64 → Variable) (order : Order) (rank : UInt64 → UInt64)
    (result : Result r θ fr (fun j => name (rank j)) out)
    (sorted : ∀ j ∈ slots out, (name (rank j)).sort = sig.acSort f) :
    Denotes r θ fr name order (out.map (AnswerProjection.tagArm rank)) := by
  classical
  obtain ⟨pairs, eqn, rep, complete, _⟩ := result
  let raw (b : {b // b ∈ pairs}) := b.val.2
  let arm (b : {b // b ∈ pairs}) := AnswerProjection.tagArm rank b.val.1
  have each (b : {b // b ∈ pairs}) :=
    materializes fr name order rank b.val.1 b.val.2 (rep b.val b.property).1 (rep b.val b.property).2
      (fun row hr j hj => sorted j (by
        rw [eqn]
        exact List.mem_flatMap.mpr ⟨b.val.1, by simpa using List.mem_map_of_mem (f := Prod.fst) b.property,
          List.mem_flatMap.mpr ⟨row, hr, hj⟩⟩))
  let packet (b : {b // b ∈ pairs}) := (each b).choose
  let decoded (b : {b // b ∈ pairs}) := FactoredAnswer.readBindings (packet b)
  have changes (b : {b // b ∈ pairs}) (_ : b ∈ pairs.attach) :
      FactoredAnswer.ArmEquivalent (FactoredAnswer.live r.problem θ) (raw b) (decoded b) :=
    ⟨instance_of_equiv (fun v => ((each b).choose_spec.2 v).symm) _,
      instance_of_equiv (each b).choose_spec.2 _⟩
  have before : CompleteSet r.problem (pairs.attach.map fun b => (raw b).compose θ) := by
    rw [show (pairs.attach.map fun b => (raw b).compose θ) = _ from
      List.attach_map_val (f := fun b : Branch sig => b.2.compose θ)]
    exact complete
  have after := (FactoredAnswer.composed_set_equivalent r.problem θ pairs.attach raw decoded changes).preserves_complete before
  refine ⟨pairs.attach.map packet, ?_, ?_, ?_⟩
  · have arms : (out.map (AnswerProjection.tagArm rank)).toList = pairs.attach.map arm := by
      rw [eqn, Array.toList_map, List.toList_toArray, List.map_map]
      exact (List.attach_map_val (f := fun b : Branch sig => AnswerProjection.tagArm rank b.1)).symm
    rw [arms, List.map_map]
    exact mapM_map pairs.attach _ arm _ (fun b => (each b).choose_spec.1)
  · simpa only [List.map_map,Function.comp_def] using after
  · simpa only [List.map_map,Function.comp_def] using FreshAnswer.freshen_correct r _ after

/-- The projection contract transfers finite sorting, freshness and injectivity
to the original slot names. The caller need only define their allocation on
ordinals that appear in the delivered packet. -/
theorem of_projection {project : AnswerProjection.Kernel} (proj : AnswerProjection.Correct project)
    {f : sig.ACSym} {rows n} {fr : Frame f rows n.toNat} {r : Request sig} {θ : Substitution sig}
    {raw out : Answers} (ran : project n raw = some out)
    (solver : ∀ w : UInt64 → Variable,
      (∀ i ∈ slots raw, ∀ j ∈ slots raw, w i = w j → i = j) →
      (∀ j ∈ slots raw, (w j).sort = sig.acSort f) →
      (∀ j ∈ slots raw, w j ∉ variables rows ++ FactoredAnswer.liveKeys r.problem θ) →
      Result r θ fr w raw)
    (name : UInt64 → Variable) (order : Order)
    (inj : ∀ i ∈ ordinals out, ∀ j ∈ ordinals out, name i = name j → i = j)
    (typed : ∀ j ∈ ordinals out, (name j).sort = sig.acSort f)
    (fresh : ∀ j ∈ ordinals out, name j ∉ variables rows ++ FactoredAnswer.liveKeys r.problem θ) :
    Denotes r θ fr name order out := by
  obtain ⟨adm, rfl⟩ := (proj ..).mp ran
  let rank := AnswerProjection.rank raw
  have live {j} (hj : j ∈ slots raw) := live_rank (rank := rank) hj
  have hs (j) (hj : j ∈ slots raw) := typed (rank j) (live hj)
  apply lifts fr name order rank _ hs
  exact solver _ (fun i hi j hj eq => AnswerProjection.rank_injective adm hi hj
    (inj _ (live hi) _ (live hj) eq)) hs (fun j hj => fresh (rank j) (live hj))

/-- Full factored path from fixed shared graph and column identities to caller-visible
finite residual bindings under any chosen ordering of AC factors. -/
def Checked (check : FactorCheck.Kernel) (solve : GraphUnification.Kernel)
    (project : AnswerProjection.Kernel) : Prop :=
  ∀ {s : Signature} (r : Request s) (θ : Substitution s) (f : s.ACSym) (rows : List Row)
    (g : Input s), g.Represents r.problem θ (problem f rows) →
    check g.decls g.nodes g.original g.bindings g.residual = true →
    ∀ (n : UInt64) (fr : Frame f rows n.toNat), (∀ i, g.codec.vars.put (fr.names i) = i.val.toUInt64) →
    ∀ raw, solve n (g.codec.acs.put f) (WholeProblem.sortWord (s.acSort f))
      g.decls g.nodes g.residual = some raw →
    ∀ out, project n raw = some out →
    ∀ (name : UInt64 → Variable) (order : Order),
    (∀ i ∈ ordinals out, ∀ j ∈ ordinals out, name i = name j → i = j) →
    (∀ j ∈ ordinals out, (name j).sort = s.acSort f) →
    (∀ j ∈ ordinals out, name j ∉ variables rows ++ FactoredAnswer.liveKeys r.problem θ) →
    Denotes r θ fr name order out

theorem checked_correct {check solve project} (solver : GraphUnification.Checked check solve)
    (proj : AnswerProjection.Correct project) : Checked check solve project := by
  intro sig r θ f rows g layout accepted n fr cols raw ran out projected name order inj sorted fresh
  exact of_projection proj projected (solver r θ f rows g layout accepted n fr cols raw ran)
    name order inj sorted fresh

/-- For the direct graph path any solution instantiates one concrete caller table.
This is also true of nonground solutions and holds when the answer list is empty. -/
theorem solves_iff {solve project} (graph : GraphUnification.Correct solve)
    (proj : AnswerProjection.Correct project) {f : sig.ACSym} {rows : List Row} {n : UInt64}
    (c : WholeProblem.Codec sig) (fr : Frame f rows n.toNat) (cols : ∀ i, c.vars.put (fr.names i) = i.val.toUInt64)
    {ds ns roots p} (dec : Whole.Wire.decodeProblem ds ns roots = some p)
    (rowsRep : CheckedFactoring.Rows c (problem f rows) p) {raw out}
    (solved : solve n (c.acs.put f) (WholeProblem.sortWord (sig.acSort f)) ds ns roots = some raw)
    (projected : project n raw = some out) (name : UInt64 → Variable) (order : Order)
    (inj : ∀ i ∈ ordinals out, ∀ j ∈ ordinals out, name i = name j → i = j)
    (typed : ∀ j ∈ ordinals out, (name j).sort = sig.acSort f)
    (fresh : ∀ j ∈ ordinals out, name j ∉ variables rows) :
    ∃ packets : List (FreshAnswer sig),
      out.toList.mapM (readArm fr.names f name order) = some (packets.map FreshAnswer.bindings) ∧
      ∀ ρ, (problem f rows).Solves ρ ↔
        ∃ b ∈ packets, Substitution.InstanceOn (problem f rows).Occurs ρ (FactoredAnswer.readBindings b) := by
  let q := problem f rows
  have fact := (FactoredUnification.Trace.done q Substitution.identity).factoring
  have safe (j) (hj : j ∈ ordinals out) :
      name j ∉ variables rows ++ FactoredAnswer.liveKeys q .identity := by
    rw [List.mem_append, not_or]
    refine ⟨fresh j hj, fun hm => ?_⟩
    obtain ⟨v, hv, e⟩ := FactoredAnswer.mem_liveKeys.mp hm
    change name j = v at e
    exact fresh j hj (e ▸ (occurs_iff_mem f rows v).mp hv)
  obtain ⟨packets, decoded, cs, _⟩ := of_projection (r := ⟨q,[]⟩) proj projected
    (graph.semantic ⟨q,[]⟩ .identity f rows n fr fact c _ _ _ p dec rowsRep cols raw solved)
    name order inj typed safe
  refine ⟨packets,decoded,fun ρ => ?_⟩
  rw [cs.solves_iff ρ]
  constructor
  · rintro ⟨_,hm,h⟩
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    exact ⟨b,hb,h⟩
  · rintro ⟨b,hb,h⟩
    exact ⟨_,List.mem_map_of_mem hb,h⟩

end Tamarin.ProjectedBindings
