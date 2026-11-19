import Tamarin.OperandRefinement
import Tamarin.ResidualRigid
import Tamarin.ACRowElimination

/-! Select original equations by the identities of their peeled sides.
Every descent must preserve the equation in both directions for every
substitution. The numeric selector can then keep any representative. -/
namespace Tamarin.ContextRowSelection
open OperandRefinement
variable {sig : Signature}

abbrev Cancel := Array UInt64 → Array UInt64 → Array (Array UInt64)

/-- A one-hole free context can be removed when all its other children
agree modulo B. The AC step consumes the complete common-occurrence packet
and requires one surviving occurrence on each side. -/
inductive Peels (rigid : ResidualRigid.Kernel) (cancel : Cancel) :
    Equation sig → Equation sig → Prop where
  | stop (e) : Peels rigid cancel e e
  | free (a b : ResidualRigid.View sig) (head : Head sig → UInt64)
      (faithful : a.kind = b.kind → head a.head = head b.head → a.head = b.head)
      (put : Term sig → UInt64) (get : UInt64 → Option (Term sig))
      (live : ∀ t ∈ a.args ++ b.args, get (put t) = some t)
      (positional : rigid a.kind (head a.head) (a.words put) b.kind (head b.head) (b.words put) = 5)
      (i : Nat) {l r : Term sig} (left : a.args[i]? = some l) (right : b.args[i]? = some r)
      (siblings : ∀ j, j ≠ i → ∀ u v, a.args[j]? = some u → b.args[j]? = some v → EquivB u v)
      {core} (inside : Peels rigid cancel ⟨l,r⟩ core) :
      Peels rigid cancel ⟨a.term,b.term⟩ core
  | ac (f : sig.ACSym) (get : UInt64 → Term sig) (xs ys : Array UInt64) {e : Equation sig}
      (repr : ACRowElimination.Represents ⟨xs.toList,ys.toList⟩ f get e)
      (l r : UInt64) (residue : cancel xs ys = #[#[l],#[r]])
      {core} (inside : Peels rigid cancel ⟨get l,get r⟩ core) :
      Peels rigid cancel e core

private theorem freeViews {a b : ResidualRigid.View sig} (h : Residual.Justified 5 a.term b.term) :
    ∃ f xs ys, a = .free f xs ∧ b = .free f ys := by
  cases a <;> cases b <;> cases h
  exact ⟨_,_,_,rfl,rfl⟩

/-- The peeled equation is a bidirectional test on one simultaneous
substitution, even if discarded siblings contain variables. -/
theorem Peels.solves {rigid cancel} (hr : ResidualRigid.Correct rigid) (hc : CommonCancellation.Correct cancel)
    {a b : Equation sig} (trace : Peels rigid cancel a b) (σ : Substitution sig) :
    EquivB (σ.apply a.lhs) (σ.apply a.rhs) ↔ EquivB (σ.apply b.lhs) (σ.apply b.rhs) := by
  induction trace with
  | stop => rfl
  | free a b head faithful put get live pos i left right siblings _ ih =>
    have justified := (hr a b head faithful put get live).1
    rw [pos] at justified
    obtain ⟨f,xs,ys,rfl,rfl⟩ := freeViews justified
    have hi : i < sig.arity f := by simpa [ResidualRigid.View.args] using (List.getElem?_eq_some_iff.mp left).choose
    let k : Fin (sig.arity f) := ⟨i,hi⟩
    have l := (List.getElem?_eq_some_iff.mp left).choose_spec
    have r := (List.getElem?_eq_some_iff.mp right).choose_spec
    simp only [ResidualRigid.View.args,List.getElem_ofFn] at l r
    rw [← ih,← l,← r]
    change EquivB (.free f (fun j => σ.apply (xs j))) (.free f (fun j => σ.apply (ys j))) ↔
      EquivB (σ.apply (xs k)) (σ.apply (ys k))
    rw [Matching.free_equiv_iff]
    refine ⟨fun h => h k,fun selected j => ?_⟩
    by_cases same : j.val = i
    · exact (Fin.ext same : j = k) ▸ selected
    · exact (siblings j.val same (xs j) (ys j)
        (by simp [ResidualRigid.View.args,j.isLt]) (by simp [ResidualRigid.View.args,j.isLt])).subst σ.image
  | ac f get xs ys repr l r packet _ ih =>
    obtain ⟨left,right,ran,ok⟩ := ACResidual.run_correct hc get f xs ys
    rw [packet] at ran
    simp at ran
    obtain ⟨rfl,rfl⟩ := ran
    obtain ⟨⟨u,hu,eu⟩,⟨v,hv,ev⟩⟩ := repr
    have eq := ok σ
    change ACRepresentation.decode f (xs.toList.map get) = some u at hu
    change ACRepresentation.decode f (ys.toList.map get) = some v at hv
    unfold ACResidual.Holds at eq
    rw [hu,hv] at eq
    change EquivB (σ.apply u) (σ.apply v) ↔ EquivB (σ.apply (get l)) (σ.apply (get r)) at eq
    exact Iff.trans ⟨fun h => (eu.subst σ.image).symm.trans (h.trans (ev.subst σ.image)),
      fun h => (eu.subst σ.image).trans (h.trans (ev.subst σ.image).symm)⟩ (eq.trans ih)

/-- Pair each original row with the key used for selection. A trace may
stop at any depth, independently for every occurrence. -/
def Semantic (rigid : ResidualRigid.Kernel) (cancel : Cancel) (select : Kernel) : Prop :=
  ∀ {s : Signature} (rows : List (Equation s × Equation s)), rows.length ≤ UInt64.size →
    (∀ pair ∈ rows, Peels rigid cancel pair.1 pair.2) →
    ∀ id lookup, Encodes (rows.map Prod.snd) id lookup →
    let p : Problem s := rows.map Prod.fst
    let indices := select (wire ((rows.map Prod.snd).map (rowOf id))).toArray
    let q := reduced p indices
    (∀ i ∈ indices.toList, i.toNat < p.length) ∧ indices.size ≤ p.length ∧
    (∀ σ, p.Solves σ ↔ q.Solves σ) ∧
    (∀ observed θ ρ, Residual.Denotes observed p θ ρ ↔ Residual.Denotes observed q θ ρ) ∧
    ∀ avoid answers, (Outcome.complete answers).CorrectIn q (p.variables ++ avoid) →
      (Outcome.complete answers).CorrectIn p avoid

theorem semantic {rigid cancel select} (hr : ResidualRigid.Correct rigid) (hc : CommonCancellation.Correct cancel)
    (checked : Correct select) : Semantic rigid cancel select := by
  intro s rows bound traces id lookup table p indices q
  let keys : Problem s := rows.map Prod.snd
  have valid := OperandRefinement.semantic checked keys (by simpa [keys] using bound) id lookup table
  have aligned (pairs : List (Equation s × Equation s)) (sub : ∀ e ∈ pairs, e ∈ rows)
      (σ : Substitution s) : Problem.Solves (pairs.map Prod.fst) σ ↔ Problem.Solves (pairs.map Prod.snd) σ := by
    simp only [Problem.Solves,List.forall_mem_map]
    exact forall_congr' fun pair => forall_congr' fun h => (traces pair (sub pair h)).solves hr hc σ
  let selected := indices.toList.filterMap fun i => rows[i.toNat]?
  have pick (g : Equation s × Equation s → Equation s) :
      reduced (rows.map g) indices = selected.map g := by
    simp only [reduced,selected,List.map_filterMap,List.getElem?_map]
  have kept (e) (he : e ∈ selected) : e ∈ rows := by
    obtain ⟨_,_,h⟩ := List.mem_filterMap.mp he
    exact List.mem_of_getElem? h
  have eq (σ : Substitution s) : p.Solves σ ↔ q.Solves σ := by
    have roots := OperandRefinement.solves_iff checked keys (by simpa [keys] using bound) id table σ
    change keys.Solves σ ↔ (reduced (rows.map Prod.snd) indices).Solves σ at roots
    rw [pick] at roots
    change _ ↔ (reduced (rows.map Prod.fst) indices).Solves σ
    rw [pick]
    exact (aligned rows (fun _ h => h) σ).trans (roots.trans (aligned selected kept σ).symm)
  refine ⟨by simpa only [p,keys,indices,List.length_map] using valid.1,by simpa only [p,keys,indices,List.length_map] using valid.2.1,eq,
    fun obs θ ρ => Residual.equivalent obs eq θ ρ,?_⟩
  intro avoid answers solved
  apply ACResidual.lift_complete p q avoid p.variables answers eq _ _ solved
  · rintro v ⟨e,he,occ⟩
    obtain ⟨i,_,h⟩ := List.mem_filterMap.mp he
    exact ⟨e,List.mem_of_getElem? h,occ⟩
  · exact fun v hv _ => (p.mem_variables v).mpr hv

end Tamarin.ContextRowSelection
