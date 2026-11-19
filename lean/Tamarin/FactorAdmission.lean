import Tamarin.FactorCheck

/-! A lower bound on successful validation. The accepted proposals in this
fragment are specified using only the fixed wire syntax and sort relation. -/
namespace Tamarin.FactorAdmission
open Whole FactorCheck

/-- The sort of a leaf or the declared output sort of an application. -/
inductive ResultSort (ds : List Decl) : Tree → UInt64 → Prop where
  | leaf (k i s) : ResultSort ds (.leaf k i s) s
  | app (k i args d) (found : ds.find? (fun x => x.kind == k && x.id == i) = some d) :
    ResultSort ds (.app k i args) d.output

/-- Syntactic absence of a particular variable, under every constructor. -/
def Omits (key : Tree) : Tree → Prop
  | t@(.leaf ..) => t ≠ key
  | .app _ _ xs => ∀ t ∈ xs, Omits key t

/-- One sorted variable binding and zero or more independent residual
equations with an AC head on the left. Input order is arbitrary and the
variable's image may be compound. -/
inductive Fragment (ds : List Decl) (original bindings residual : Equations) : Prop where
  | direct (v s : UInt64) (rhs : Tree) (actual : UInt64)
      (sort : ResultSort ds rhs actual) (compatible : subsort actual s = true)
      (occurs : Omits (.leaf 0 v s) rhs)
      (roots : original.Perm ((.leaf 0 v s, rhs) :: residual))
      (factor : bindings = [(.leaf 0 v s, rhs)])
      (remaining : ∀ e ∈ residual, (∃ f xs, e.1 = .app 4 f xs) ∧
        Omits (.leaf 0 v s) e.1 ∧ Omits (.leaf 0 v s) e.2) :
      Fragment ds original bindings residual

/-- Every successfully decoded proposal in the fragment must be accepted.
This obligation quantifies over arbitrary numeric IDs and graph layouts. -/
def Required (candidate : Kernel) : Prop :=
  ∀ ds ns os bs rs d ts p b q,
    declarations ds.toList = some d → decodeNodes d ns = some ts →
    readEquations ts os.toList = some p → readEquations ts bs.toList = some b →
    readEquations ts rs.toList = some q → Fragment d p b q → candidate ds ns os bs rs = true

private theorem sort_eq {ds rhs s} (h : ResultSort ds rhs s) : rootSort ds rhs = some s := by
  cases h with
  | leaf => rfl
  | app _ _ _ _ found => simp [rootSort, found]

mutual
  private theorem unchanged (v s : UInt64) (rhs t : Tree) (h : Omits (.leaf 0 v s) t) :
      applyBindings [(.leaf 0 v s,rhs)] t = t := by
    cases t with
    | leaf k i u =>
      simp only [Omits] at h
      by_cases kind : k = 0
      · subst k
        simp [applyBindings, lookup, Ne.symm h]
      · simp [applyBindings, kind]
    | app k i xs =>
      exact congrArg (Tree.app k i) (unchangedArgs v s rhs xs (by simpa only [Omits] using h))
  private theorem unchangedArgs (v s : UInt64) (rhs : Tree) (xs : List Tree)
      (h : ∀ t ∈ xs, Omits (.leaf 0 v s) t) :
      applyChildren [(.leaf 0 v s,rhs)] xs = xs := by
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [applyChildren, unchanged v s rhs x (h _ List.mem_cons_self),
        unchangedArgs v s rhs xs (fun t ht => h t (List.mem_cons_of_mem _ ht))]
end

private theorem supports_mem (q : Equations) {e : Tree × Tree} (h : e ∈ q) :
    supported q e = true := by
  simp only [supported, Bool.or_eq_true]
  exact Or.inr (List.any_eq_true.mpr ⟨e,h,by simp [same]⟩)

theorem accepts {ds p bs q} (h : Fragment ds p bs q) : check ds p bs q = true := by
  obtain ⟨v,s,rhs,actual,hs,compat,absent,perm,rfl,remaining⟩ := h
  let key := Tree.leaf 0 v s
  let θ := [(key,rhs)]
  have rhs_fixed : applyBindings θ rhs = rhs := unchanged v s rhs rhs absent
  have var_image : applyBindings θ key = rhs := by simp [θ,key,applyBindings,lookup]
  have fixed (e) (he : e ∈ q) : applyBindings θ e.1 = e.1 ∧ applyBindings θ e.2 = e.2 :=
    ⟨unchanged v s rhs _ (remaining e he).2.1, unchanged v s rhs _ (remaining e he).2.2⟩
  have flat : p.flatMap (fun e => expose 128 e.1 e.2) = p := by
    have each (e) (he : e ∈ p) : expose 128 e.1 e.2 = [e] := by
      rcases List.mem_cons.mp (perm.mem_iff.mp he) with rfl | hq
      · rfl
      · obtain ⟨f,xs,hl⟩ := (remaining e hq).1
        obtain ⟨a,b⟩ := e
        simp only at hl
        subst a
        rfl
    clear perm
    induction p with
    | nil => rfl
    | cons u us ih =>
      rw [List.flatMap_cons, each u List.mem_cons_self, ih (fun e he => each e (List.mem_cons_of_mem _ he))]
      rfl
  have in_derived (e) (he : e ∈ q) : e ∈ substitute θ p := by
    obtain ⟨l,r⟩ := fixed e he
    exact List.mem_map.mpr ⟨e,perm.mem_iff.mpr (List.mem_cons_of_mem _ he),by simp [l,r]⟩
  have src : (key,rhs) ∈ p := perm.mem_iff.mpr List.mem_cons_self
  have sorts : sortedBinding ds (key,rhs) = true := by simp [key, sortedBinding, sort_eq hs, compat]
  apply Bool.or_eq_true_iff.mpr; apply Or.inl
  simp only [direct,flat]
  change ([ (key,rhs) ].all _ && _ && [ (key,rhs) ].all _ && q.all _ &&
    (substitute θ p).all _ && q.all _) = true
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨by simpa using sorts, by simp [List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,List.isEqv]⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have hit : p.any (same (key,rhs)) = true :=
      List.any_eq_true.mpr ⟨_,src,by simp [same]⟩
    simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,beq_iff_eq]
    exact ⟨rhs_fixed,hit⟩
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨l,r⟩ := fixed e he
    rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.mpr l, beq_iff_eq.mpr r⟩
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨srcE,hs,rfl⟩ := List.mem_map.mp he
    rcases List.mem_cons.mp (perm.mem_iff.mp hs) with rfl | hq
    · rw [supported, Bool.or_eq_true]; exact (.inl (beq_iff_eq.mpr (var_image.trans rhs_fixed.symm)))
    · obtain ⟨l,r⟩ := fixed srcE hq
      simpa only [l,r] using supports_mem q hq
  · exact List.all_eq_true.mpr fun e he => supports_mem _ (in_derived e he)

theorem run_required : Required FactorCheck.run := by
  intro ds ns os bs rs d ts p b q hd ht hp hb hq h
  simpa [FactorCheck.run, FactorCheck.runWith, hd, ht, hp, hb, hq] using accepts h

/-- A chain whose first image is specialized by the second elimination.
The same coverage obligation applies to any shared graph and node ordering
that decodes to these equations. -/
def ChainRequired (candidate : Kernel) : Prop :=
  let x := Tree.leaf 0 0 2
  let y := Tree.leaf 0 1 2
  let a := Tree.leaf 1 0 2
  ∀ ds ns os bs rs decl trees, declarations ds.toList = some decl → decodeNodes decl ns = some trees →
    readEquations trees os.toList = some [(x,y),(y,a)] →
    readEquations trees bs.toList = some [(x,a),(y,a)] →
    readEquations trees rs.toList = some [] → candidate ds ns os bs rs = true

theorem run_chain : ChainRequired FactorCheck.run := by
  intro ds ns os bs rs decl trees hd ht hp hb hr
  simp only [FactorCheck.run,FactorCheck.runWith,hd,ht,hp,hb,hr]
  rfl

end Tamarin.FactorAdmission
