import Tamarin.MixedConstructorRows
import Tamarin.CheckedReduction
import Tamarin.TableNarrowing
import Tamarin.MixedUnification
import Tamarin.FrontierWork

/-! Ground outputs of competing constructor-pattern rules can require
further rewriting. Check the finitely many fixed output terms against the
whole table, then lift their agreement to every normalized substitution. -/
namespace Tamarin.ConstructorRows
open Rewriting ConstructorVariants ContextualReduction
variable {s : Signature} {rs : Problem s} {r : Equation s}

structure GroundRow (rs : Problem s) (r : Equation s) : Prop where
  pattern : Pattern rs r.lhs
  ground : r.rhs.Ground
  results : r ∈ rs → (∀ q ∈ rs, Application q.lhs) → ∃ v, ∀ (σ : Substitution s) z, AtRoot (ruleRoot rs) (σ.apply r.lhs) z →
    ∀ u, Reduces (ruleRoot rs) z u → Normal (ruleRoot rs) u → EquivB u v

theorem GroundRow.subterm (ok : GroundRow rs r) (_mem : r ∈ rs) : SubtermVariants.Row r := by
  have pat := ok.pattern
  cases h : r.lhs <;> simp [SubtermVariants.Row,Pattern,h,ok.ground] at *

theorem GroundRow.unique (ok : GroundRow rs r) (mem : r ∈ rs) (apps : ∀ q ∈ rs, Application q.lhs)
    (σ : Substitution s) (norm : Normalized (ruleRoot rs) σ) {a b}
    (left : NormalForm (ruleRoot rs) (σ.apply r.lhs) a) (right : NormalForm (ruleRoot rs) (σ.apply r.lhs) b) :
    EquivB a b := by
  obtain ⟨v,all⟩ := ok.results mem apps
  have fire : StepModulo (ruleRoot rs) (σ.apply r.lhs) (σ.apply r.rhs) :=
    ⟨_,_,.refl _,.root ⟨r,mem,σ,rfl,rfl⟩,.refl _⟩
  have endpoint {u} (nf : NormalForm (ruleRoot rs) (σ.apply r.lhs) u) : EquivB u v := by
    rcases RootNarrowing.firstStep nf.1 with same | ⟨z,st,tail⟩
    · exact (((normal_equiv _ same).mpr nf.2.1) _ fire).elim
    exact all σ z (root_of_pattern apps σ norm ok.pattern st) u tail nf.2.1
  exact (endpoint left).trans (endpoint right).symm

private theorem ground_of_empty {t : Term s} (h : t.variables.isEmpty) : t.Ground :=
  fun w occ => (List.eq_nil_iff_forall_not_mem.mp (List.isEmpty_iff.mp h) w) ((Term.mem_variables ..).mpr occ)

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- A closed constructor expression is already irreducible in the whole
table. Other fixed outputs can use the bounded all-path reduction check. -/
private def agrees (rs : Problem s) (v : Term s) (fuel : Nat) (t : Term s) : Bool :=
  if constructorPattern rs t then t == v || ReferenceMatching.equal t v else CheckedReduction.agrees rs v fuel t

private theorem agrees_sound (scope : ReferenceReduction.Bound rs) (apps : ∀ q ∈ rs, Application q.lhs)
    {t v fuel u} (ok : agrees rs v fuel t) (path : Reduces (ruleRoot rs) t u) (nf : Normal (ruleRoot rs) u) : EquivB u v := by
  unfold agrees at ok
  split at ok
  · rename_i pat
    have normal := (constructor_normal rs apps).2 t ((constructorPattern_iff ..).mp pat)
      Substitution.identity (constructor_normal rs apps).1
    rw [Substitution.apply_identity] at normal
    have eq : EquivB t v := (Bool.or_eq_true_iff.mp ok).elim
      (fun h => eq_of_beq h ▸ .refl _) ((ReferenceMatching.equal_iff ..).mp)
    exact (normal_reduces_equiv path normal).symm.trans eq
  · exact CheckedReduction.agrees_sound scope v fuel t u ok path nf

/-- Each same-head competitor can certify its fixed output without unification.
Only the remaining pairs enter narrowing, subject to the admission work bound.
All ground endpoint checks use the complete active table. -/
private def pairResults (rs : Problem s) (r q : Equation s) (v : Term s) (fuel : Nat) : Bool :=
  !headEq (head q.lhs) (head r.lhs) ||
  (q.rhs.variables.isEmpty && agrees rs v fuel q.rhs) ||
  (FrontierWork.admitsRootPair r.lhs q.lhs &&
    if scope : CheckedReduction.rangeBound [q] then
      (TableNarrowing.roots MixedUnification.verified ((CheckedReduction.rangeBound_iff [q]).mp scope) [] r.lhs).all
        fun b => b.value.variables.isEmpty && agrees rs v fuel b.value
    else false)

/-- Only competing instances of these very constructor patterns need agree.
The complete ordinary unifier supplies the overlaps modulo C/AC. A competing
rule may return a variable that the overlap specializes to a ground value. -/
def groundRow (rs : Problem s) (fuel : Nat) (r : Equation s) : Bool :=
  pattern rs r.lhs && r.rhs.variables.isEmpty &&
    (if constructorPattern rs r.rhs then some r.rhs else CheckedReduction.choose rs fuel r.rhs).any fun v =>
      rs.all fun q => pairResults rs r q v fuel

theorem groundRow_sound (scope : ReferenceReduction.Bound rs) {fuel}
    (accepted : groundRow rs fuel r) : GroundRow rs r := by
  simp only [groundRow,Bool.and_eq_true] at accepted
  obtain ⟨⟨pat,clean⟩,all⟩ := accepted
  refine ⟨(pattern_iff ..).mp pat,ground_of_empty clean,fun mem apps => ?_⟩
  generalize h : (if constructorPattern rs r.rhs then some r.rhs else CheckedReduction.choose rs fuel r.rhs) = choice at all
  cases choice with
  | none => contradiction
  | some v =>
    refine ⟨v,?_⟩
    rintro σ z ⟨_,_,pre,⟨q,hq,τ,rfl,rfl⟩,post⟩ u path nf
    have same := (instance_head q (apps q hq) τ).symm.trans (pre.head_eq.symm.trans (instance_head r (apps r mem) σ))
    have pair := List.all_eq_true.mp all q hq
    simp only [pairResults,(headEq_iff (head q.lhs) (head r.lhs)).mpr same,
      Bool.not_true,Bool.false_or,Bool.or_eq_true,Bool.and_eq_true] at pair
    rcases pair with ⟨clean,result⟩ | ⟨_,overlaps⟩
    · rw [(ground_of_empty clean).apply_eq τ] at post
      exact agrees_sound scope apps result ((Reduces.basis post).trans path) nf
    · have localScope : ReferenceReduction.Bound [q] := by
        intro t ht; obtain rfl := List.mem_singleton.mp ht; exact scope _ hq
      rw [dite_eq_left ((CheckedReduction.rangeBound_iff [q]).mpr localScope)] at overlaps
      have fire : AtRoot (ruleRoot [q]) (σ.apply r.lhs) z :=
        ⟨_,_,pre,⟨q,List.mem_cons_self,τ,rfl,rfl⟩,post⟩
      obtain ⟨b,hb,δ,_,fit⟩ := TableNarrowing.roots_cover MixedUnification.verified localScope [] r.lhs σ fire
      obtain ⟨fixed,ok⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp overlaps b hb)
      rw [(ground_of_empty fixed).apply_eq δ] at fit
      exact agrees_sound scope apps ok ((Reduces.basis fit.symm).trans path) nf

end Tamarin.ConstructorRows
