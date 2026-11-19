import Tamarin.ProjectedBindings

/-! Opening the dense fresh-range table returned on a checked factorization.
Rust may enumerate observed variables in its own order. The caller chooses
fresh names locally and uses the same renaming for every image of an arm. -/
namespace Tamarin.DenseOpening
open ProjectedBindings ACSystem Homogeneous
variable {sig : Signature}

/-- The local first-free index allocator discharges the semantic name conditions.
The caller's embedding of a full variable identity and its reserved-index inventory
are the only name information in the statement. Neither is an ABI argument. -/
theorem allocated {check graph project} (verified : ProjectedBindings.Checked check graph project)
    (projection : AnswerProjection.Correct project) (r : Request sig) (θ : Substitution sig)
    (f : sig.ACSym) (rows : List Row) (g : FactoredAC.Input sig)
    (layout : g.Represents r.problem θ (problem f rows))
    (accept : check g.decls g.nodes g.original g.bindings g.residual = true)
    (n : UInt64) (fr : Frame f rows n.toNat) (cols : ∀ i, g.codec.vars.put (fr.names i) = i.val.toUInt64)
    {raw out} (ran : graph n (g.codec.acs.put f) (WholeProblem.sortWord (sig.acSort f))
      g.decls g.nodes g.residual = some raw) (projected : project n raw = some out)
    (reserved : UInt64 → Bool) {ws} (alloc : OrdinalAllocation.allocate reserved
      (AnswerProjection.keys raw).length = some ws)
    (make : UInt64 → Variable) (injective : Function.Injective make)
    (typed : ∀ i, (make i).sort = sig.acSort f)
    (occupied : ∀ i, make i ∈ variables rows ++ FactoredAnswer.liveKeys r.problem θ → reserved i = true)
    (order : Order) : Denotes r θ fr (OrdinalAllocation.nameAt make ws) order out := by
  obtain ⟨inj, types, fresh⟩ := allocated_names projection projected reserved alloc
    make injective _ typed _ occupied
  exact verified r θ f rows g layout accept n fr cols raw ran out projected _ order inj types fresh

/-- Tabulate the ordinary composition on the domain of the original query.
In particular, a stored identity shares its range name with any other image
that contains it when the caller opens the answer. -/
def close (observed : List Variable) (θ : Substitution sig) (residual : FreshAnswer sig) :=
  FreshAnswer.encode observed ((FactoredAnswer.readBindings residual).compose θ)

private def rename {sources : List Variable} (a : CallerFreshening.Allocation sources)
    (w : Variable) : Term sig :=
  if w ∈ sources then .var (a.assign w) else .var w

private theorem rename_sorted {sources} (a : CallerFreshening.Allocation sources) (w : Variable) :
    HasSort (rename (sig := sig) a w) w.sort := by
  unfold rename
  split
  · next hw => rw [← a.sorted w hw]; exact .var _
  · exact .var _

/-- Open every explicitly stored binding with one finite caller allocation. -/
def openPacket (b : FreshAnswer sig) {sources} (a : CallerFreshening.Allocation sources) : Substitution sig :=
  Substitution.fromBindings (b.bindings.map fun (v,t) => (v, t.subst (rename a))) (by
    intro v t ht
    obtain ⟨⟨u,x⟩, h, eq⟩ := List.mem_map.mp ht
    cases eq
    exact (b.sorted _ x h).subst _ (rename_sorted a))

private theorem represents (p : Problem sig) (observed : List Variable)
    (live : ∀ v, v ∈ observed ↔ p.Occurs v) (σ : Substitution sig)
    (a : CallerFreshening.Allocation (CallerFreshening.sources p σ)) :
    CallerFreshening.Represents p σ (openPacket (FreshAnswer.encode observed σ) a) a := by
  intro v
  simp only [openPacket, FreshAnswer.encode, Substitution.fromBindings, List.map_map, Function.comp_def]
  rw [Substitution.lookupBinding_tabulate]
  by_cases hv : v ∈ observed
  · rw [ite_eq_left hv, ite_eq_left ((p.mem_variables v).mpr ((live v).mp hv))]
    apply Term.subst_eq_of_agree
    intro w hw
    exact ite_eq_left (List.mem_flatMap.mpr ⟨v, (p.mem_variables v).mpr ((live v).mp hv),
      ((σ.image v).mem_variables w).mpr hw⟩)
  · rw [ite_eq_right hv, ite_eq_right (fun h => hv ((live v).mpr ((p.mem_variables v).mp h)))]

/-- Caller-visible correctness of the dense tables, from the projected packet
and the caller's finite allocation. There is no per-arm equivalence premise. -/
theorem correct {f : sig.ACSym} {rows n} {r : Request sig} {θ : Substitution sig}
    {fr : Frame f rows n} {name order out} (h : Denotes r θ fr name order out)
    (observed : List Variable) (live : ∀ v, v ∈ observed ↔ r.problem.Occurs v) :
    ∃ bs : List (FreshAnswer sig),
      out.toList.mapM (readArm fr.names f name order) = some (bs.map FreshAnswer.bindings) ∧
      ∀ alloc : (b : FreshAnswer sig) → CallerFreshening.Allocation
        (CallerFreshening.sources r.problem ((FactoredAnswer.readBindings b).compose θ)),
        (∀ b ∈ bs, CallerFreshening.Avoids r ((FactoredAnswer.readBindings b).compose θ) (alloc b)) →
        (Outcome.complete (bs.map fun b => openPacket (close observed θ b) (alloc b))).CorrectIn
          r.problem r.avoid := by
  obtain ⟨bs, decoded, complete, _⟩ := h
  refine ⟨bs, decoded, ?_⟩
  intro alloc fresh
  exact (CallerFreshening.refinement r bs _ _ alloc
    (fun b _ => represents r.problem observed live _ (alloc b)) fresh).preserves_correct complete

end Tamarin.DenseOpening
