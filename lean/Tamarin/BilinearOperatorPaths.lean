import Tamarin.BilinearRoots
import Tamarin.DHPresentation

/-! Operator bounds for the point action and the commutative bilinear map.
Each normal point exposes at most one action. Extracting it leaves only a
scalar product or a DH power on normal operands, whose bounds are already
available for the complete active table. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer ShortVariantPaths
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {T : Table s} {E : ExtraTable T}
variable (I : Inventory s β T.rules)

private theorem Rule.source_sorted (r : Rule) (v : Fin 3 → Term sig) (ty : ∀ i, HasSort (v i) .msg) :
    HasSort (r.equation s β v).lhs .msg := by
  have unit : HasSort s.product.one .msg :=
    s.oneSort ▸ HasSort.free s.one _ (fun i => Fin.elim0 (s.oneArity ▸ i))
  cases r with
  | one => exact β.point_sorted unit (ty 0)
  | nested => exact β.point_sorted (ty 0) (β.point_sorted (ty 1) (ty 2))
  | extract => exact β.map_sorted (ty 0) (β.point_sorted (ty 1) (ty 2))

include I in
theorem Inventory.redex_typed {p q : Term sig} (h : head p = .free β.pmult ∨ head p = .comm β.emap)
    (step : ruleRoot T.rules p q) : HasSort p .msg := by
  obtain ⟨r,hr,σ,rfl,rfl⟩ := step
  rw [instance_head r (I.apps r hr) σ] at h
  have src (u : Rule) : HasSort (u.equation s β (fun i => .var (I.keys u i))).lhs .msg :=
    u.source_sorted _ (fun i => I.typed u i ▸ HasSort.var _)
  rcases h with hp | hm
  · obtain ⟨u,_,rfl⟩ := I.onlyPoint r hr hp
    exact (src u).subst σ.image σ.sorted
  · obtain rfl := I.onlyMap r hr hm
    exact (src .extract).subst σ.image σ.sorted

private theorem root {R : Root sig} {a b : Term sig} (r : R a b) : Path R 1 a b :=
  .step ⟨_,_,.refl _,.root r,.refl _⟩ (.basis (.refl _))

variable [DecidableEq sig.ACSym] (dh : ProtectedTable E)

include I dh

private theorem point_paths : ∃ k, ∀ a p : Term sig, HasSort a .msg → HasSort p .msg →
    Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) p →
    ∃ u, Path (ruleRoot T.rules) k (β.point a p) u ∧ Normal (ruleRoot T.rules) u := by
  obtain ⟨k,product⟩ := product_paths dh.inventory dh.product dh.inverse dh.unit
  refine ⟨1 + sig.arity β.pmult * k + 1,fun a p ta tp na np => ?_⟩
  by_cases unit : head a = .free s.one
  · obtain rfl : a = s.product.one := nullary s.oneArity unit
    exact ⟨p,(root (I.one tp)).weaken (by omega),np⟩
  by_cases scaled : head p = .free β.pmult
  · obtain ⟨b,q,rfl⟩ := β.split scaled
    obtain ⟨tb,tq⟩ := β.point_types tp
    obtain ⟨nb,nq,_,plain⟩ := (I.point_normal_iff tb tq).mp np
    obtain ⟨m,tm,path,nm⟩ := product a b ta tb na nb
    have lift : Path (ruleRoot T.rules) (sig.arity β.pmult*k)
        (β.point (s.product.mul a b) q) (β.point m q) := by
      apply Path.free; intro i; split <;> first | exact path | exact .basis (.refl _)
    have first := (root (I.nested ta tb tq)).append lift
    by_cases one : head m = .free s.one
    · obtain rfl : m = s.product.one := nullary s.oneArity one
      exact ⟨q,first.append (root (I.one tq)),nq⟩
    · exact ⟨_,first.weaken (by omega),(I.point_normal_iff tm tq).mpr ⟨nm,nq,one,plain⟩⟩
  · exact ⟨_,.basis (.refl _),(I.point_normal_iff ta tp).mpr ⟨na,np,unit,scaled⟩⟩

theorem Inventory.free_bound : ∃ k, ∀ xs, (∀ i, Normal (ruleRoot T.rules) (xs i)) →
    ∃ u, Path (ruleRoot T.rules) k (.free β.pmult xs) u ∧ Normal (ruleRoot T.rules) u := by
  obtain ⟨k,go⟩ := point_paths I dh
  exact ⟨k,binary_free_paths β.arity β.inputs (I.redex_typed (.inl rfl)) go⟩

private theorem map_paths : ∃ k, ∀ p q : Term sig, HasSort p .msg → HasSort q .msg →
    Normal (ruleRoot T.rules) p → Normal (ruleRoot T.rules) q →
    ∃ u, Path (ruleRoot T.rules) k (β.map p q) u ∧ Normal (ruleRoot T.rules) u := by
  obtain ⟨k,power⟩ := power_paths dh.inventory dh.product dh.inverse dh.unit dh.power
  -- Once one side is plain, at most one extraction exposes a DH power.
  have plain (p q : Term sig) (tp : HasSort p .msg) (tq : HasSort q .msg)
      (np : Normal (ruleRoot T.rules) p) (nq : Normal (ruleRoot T.rules) q)
      (hp : head p ≠ .free β.pmult) :
      ∃ u, HasSort u .msg ∧ Path (ruleRoot T.rules) (1+k) (β.map p q) u ∧ Normal (ruleRoot T.rules) u := by
    by_cases hq : head q = .free β.pmult
    · obtain ⟨b,w,rfl⟩ := β.split hq
      obtain ⟨tb,tw⟩ := β.point_types tq
      obtain ⟨nb,nw,_,hw⟩ := (I.point_normal_iff tb tw).mp nq
      have base := (I.map_normal_iff tp tw).mpr ⟨np,nw,hp,hw⟩
      obtain ⟨u,tu,path,nu⟩ := power _ b (β.map_sorted tp tw) tb base nb
      exact ⟨u,tu,(root (I.extract tp tb tw)).append path,nu⟩
    · exact ⟨_,β.map_sorted tp tq,.basis (.refl _),(I.map_normal_iff tp tq).mpr ⟨np,nq,hp,hq⟩⟩
  refine ⟨1 + sig.arity s.pow * (1+k) + k,fun p q tp tq np nq => ?_⟩
  by_cases hq : head q = .free β.pmult
  · obtain ⟨b,w,rfl⟩ := β.split hq
    obtain ⟨tb,tw⟩ := β.point_types tq
    obtain ⟨nb,nw,_,hw⟩ := (I.point_normal_iff tb tw).mp nq
    obtain ⟨v,tv,path,nv⟩ := plain w p tw tp nw np hw
    have lift : Path (ruleRoot T.rules) (sig.arity s.pow*(1+k))
        (s.power (β.map p w) b) (s.power v b) := by
      apply Path.free; intro i; split
      · exact path.rebase (.comm_swap ..)
      · exact .basis (.refl _)
    obtain ⟨u,_,finish,nu⟩ := power v b tv tb nv nb
    exact ⟨u,((root (I.extract tp tb tw)).append lift).append finish,nu⟩
  · obtain ⟨u,_,path,nu⟩ := plain q p tq tp nq np hq
    exact ⟨u,(path.rebase (.comm_swap ..)).weaken (by omega),nu⟩

theorem Inventory.comm_bound : ∃ k, ∀ p q, Normal (ruleRoot T.rules) p → Normal (ruleRoot T.rules) q →
    ∃ u, Path (ruleRoot T.rules) k (.comm β.emap p q) u ∧ Normal (ruleRoot T.rules) u := by
  obtain ⟨k,go⟩ := map_paths I dh
  refine ⟨k,fun p q np nq => ?_⟩
  by_cases ty : HasSort (.comm β.emap p q) .msg
  · have h := Term.checkSort_complete ty
    simp only [Term.checkSort,Bool.and_eq_true,β.mapSort] at h
    exact go p q (Term.checkSort_sound _ _ h.1.2) (Term.checkSort_sound _ _ h.2) np nq
  · exact ⟨_,.basis (.refl _),unsorted_comm (fun h => I.redex_typed (.inr h)) np nq ty⟩

end Tamarin.Rewriting.Bilinear
