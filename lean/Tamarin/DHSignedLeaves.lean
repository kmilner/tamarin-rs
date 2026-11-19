import Tamarin.SignedGraphContract
import Tamarin.VariantComposition
import Tamarin.VariantPresentation

/-! Specialize a simultaneous signed graph to stable operand terms. They
may contain shared caller variables, have a proper subsort of Msg, or be
equal. One joint structural unification must relate all operands to a graph
arm before projecting the original caller images and the observed values. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open VariantJoin
variable {sig : Signature} {s : Symbols sig} {R : Root sig} {n : Nat} {A : Type}

/-- The wire reserves the first coordinates for input terms. Output
coordinates may be observed but cannot be referenced by the input program. -/
def Expr.withOutputs (k : Nat) : Expr n → Expr (n+k)
  | .input i => .input (i.castAdd k)
  | .unit => .unit
  | .inv a => .inv (a.withOutputs k)
  | .mul a b => .mul (a.withOutputs k) (b.withOutputs k)

private theorem Expr.withOutputs_term {k : Nat} (e : Expr n) (x : Fin n → Term sig) (y : Fin k → Term sig) :
    (e.withOutputs k).term s (Fin.addCases x y) = e.term s x := by
  induction e with
  | input i => simp [withOutputs,Expr.term]
  | unit => rfl
  | inv e h => simp only [withOutputs,Expr.term,h]
  | mul a b h j => simp only [withOutputs,Expr.term,h,j]

def outputGraph {m k : Nat} (es : Fin k → Expr m) :=
  (List.finRange k).map fun i => ((es i).withOutputs k,Fin.natAdd m i)

private theorem Expr.withOutputs_spelling {k : Nat} (e : Expr n) :
    SignedGraph.spelling (e.withOutputs k) = SignedGraph.spelling e := by
  induction e with
  | unit | input => rfl
  | inv _ ih => simp only [withOutputs,SignedGraph.spelling,ih]
  | mul _ _ l r => simp only [withOutputs,SignedGraph.spelling,l,r]

private theorem Expr.spelling_bounded (e : Expr n) : ∀ w ∈ SignedGraph.spelling e, w < 3+n := by
  induction e with
  | input i => simp [SignedGraph.spelling]
  | unit => simp [SignedGraph.spelling]; omega
  | inv _ ih => simp [SignedGraph.spelling]; grind
  | mul _ _ l r => simp [SignedGraph.spelling]; grind

theorem outputGraph_source {m : Nat} (obs : Array (Array UInt64)) (es : Fin obs.size → Expr m)
    (encoded : ∀ a, SignedGraph.spelling (es a) = obs[a].toList.map UInt64.toNat) :
    SignedGraph.Source m obs (outputGraph es) := by
  unfold SignedGraph.Source outputGraph
  generalize List.finRange obs.size = is
  induction is with
  | nil => exact .nil
  | cons a _ ih =>
    exact .cons ⟨rfl,(es a).withOutputs_spelling.trans (encoded a),
      (es a).withOutputs_spelling ▸ (es a).spelling_bounded⟩ ih

private def splitArm {m k : Nat} (s : Symbols sig) (r : SignedGraph.Arm (m+k)) : Row sig (Fin m) (Fin k) :=
  ⟨fun i => SignedGraph.imageTerm s (r (i.castAdd k)),fun a => SignedGraph.imageTerm s (r (a.natAdd m))⟩

/-- A completed packet for the original programs supplies exactly the
parent-family law used in stable_leaf_stage. A caller need not assume
output sorts in advance. Reachability and the row both imply them. -/
theorem packet_parents {solve} (correct : SignedGraph.Correct solve) (inputs : UInt64)
    (obs : Array (Array UInt64)) (es : Fin obs.size → Expr inputs.toNat)
    (width : 3 + inputs.toNat ≤ UInt64.size) (encoded : ∀ a, SignedGraph.spelling (es a) = obs[a].toList.map UInt64.toNat)
    (done : solve inputs obs ≠ #[0]) [DecidableEq sig.ACSym] {T : Table s} {E : ExtraTable T}
    (inventory : Balance.Inventory E) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) :
    ∃ arms, SignedGraph.represents (n := inputs.toNat + obs.size) arms (solve inputs obs) ∧
    ∀ x, (∀ i, HasSort (x i) .msg) → (∀ i, Normal (ruleRoot T.rules) (x i)) →
      ∀ y, (∀ a, Normal (ruleRoot T.rules) (y a)) →
        ((∀ a, NormalForm (ruleRoot T.rules) ((es a).term s x) (y a)) ↔
          ∃ p ∈ arms.map (splitArm (k := obs.size) s), Denotes (ruleRoot T.rules) p x y) := by
  obtain ⟨qs,hq,arms,packet,meaning⟩ := (correct inputs obs).resolve_left done
  obtain rfl := (outputGraph_source obs es encoded).unique width hq
  obtain ⟨well,exactGraph⟩ := meaning inventory mul inv unit
  refine ⟨arms,packet,fun x tx nx y ny => ?_⟩
  let env := Fin.addCases (motive := fun _ => Term sig) x y
  have sem (ty : ∀ a, HasSort (y a) .msg) := exactGraph env
    (Fin.addCases (by simpa [env] using tx) (by simpa [env] using ty))
    (Fin.addCases (by simpa [env] using nx) (by simpa [env] using ny))
  have forms : (∀ eq ∈ outputGraph es, NormalForm (ruleRoot T.rules) (eq.1.term s env) (env eq.2)) ↔
        ∀ a, NormalForm (ruleRoot T.rules) ((es a).term s x) (y a) := by
    simp [outputGraph,env,Expr.withOutputs_term]
  constructor
  · intro h
    obtain ⟨r,hr,δ,nd,fit⟩ := (sem (fun a => (h a).2.2 .msg ((es a).sorted s x tx))).mp (forms.mpr h)
    refine ⟨_,List.mem_map_of_mem (f := splitArm (k := obs.size) s) hr,δ,nd,?_,?_⟩
    · intro i; simpa [env,splitArm] using fit (i.castAdd obs.size)
    · intro a; simpa [env,splitArm] using fit (a.natAdd inputs.toNat)
  · rintro ⟨p,hp,δ,nd,fit⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    have ty a : HasSort (y a) .msg := Term.checkSort_sound _ _
      ((SortClash.check_equiv (fit.values a) _) ▸ Term.checkSort_complete
        ((well r hr (a.natAdd inputs.toNat)).1.subst δ.image δ.sorted))
    apply forms.mp ((sem ty).mpr ⟨r,hr,δ,nd,?_⟩)
    exact Fin.addCases (fun i => by simpa [env,splitArm] using fit.inputs i)
      (fun a => by simpa [env,splitArm] using fit.values a)

def operandRow (keys : List Variable) (leaf : Fin n → Term sig) : Row sig (Key keys) (Fin n) :=
  ⟨fun k => .var k.val,leaf⟩

/-- This is the local law required by exact_staged. It accepts any complete
parent family on normalized messages. Operand terms are stored only on the
caller side. The same substitution explains their internal variables even
when a variable also appears as a separate operand. -/
theorem stable_leaf_stage (keys : List Variable) (leaf : Fin n → Term sig)
    (typed : ∀ i, HasSort (leaf i) .msg) (stable : ∀ i, StableVariants.Stable R (leaf i))
    (scope : ∀ i v, (leaf i).Occurs v → v ∈ keys)
    (es : A → Expr n) (parents : List (Row sig (Fin n) A))
    (family : ∀ x, (∀ i, HasSort (x i) .msg) → (∀ i, Normal R (x i)) →
      ∀ y, (∀ a, Normal R (y a)) → ((∀ a, NormalForm R ((es a).term s x) (y a)) ↔
        ∃ p ∈ parents, Denotes R p x y))
    (ρ : Substitution sig) (hn : Normalized R ρ) (y : A → Term sig) (ny : ∀ a, Normal R (y a)) :
    (∀ a, NormalForm R (ρ.apply ((es a).term s leaf)) (y a)) ↔
      ∃ m, (∀ i, Normal R (m i)) ∧
        (∃ c ∈ [operandRow keys leaf], Denotes R c (fun k => ρ.image k.val) m) ∧
        ∃ p ∈ parents, Denotes R p m y := by
  let value := fun i => ρ.apply (leaf i)
  have tv i : HasSort (value i) .msg := (typed i).subst ρ.image ρ.sorted
  have nv i : Normal R (value i) := stable i ρ hn
  constructor
  · intro forms
    refine ⟨value,nv,⟨_,List.mem_singleton_self _,ρ,hn,fun _ => .refl _,fun _ => .refl _⟩,?_⟩
    exact (family value tv nv y ny).mp fun a => (es a).subst_term s leaf ρ ▸ forms a
  · rintro ⟨m,nm,⟨child,hc,δ,_,fit⟩,parent⟩
    obtain rfl := List.mem_singleton.mp hc
    have agree i : EquivB (value i) (m i) := by
      refine ((leaf i).subst_equiv ρ.image δ.image ?_).trans (fit.values i).symm
      exact fun v hv => fit.inputs ⟨v,scope i v hv⟩
    have tm i : HasSort (m i) .msg := Term.checkSort_sound _ _
      ((SortClash.check_equiv (agree i) _).symm ▸ Term.checkSort_complete (tv i))
    have forms := (family m tm nm y ny).mpr parent
    intro a
    rw [(es a).subst_term]
    exact NormalForm.equiv_input ((es a).term_equiv (s := s) agree).symm (forms a)

end Tamarin.Rewriting.DHPeer.SignedMatrix
