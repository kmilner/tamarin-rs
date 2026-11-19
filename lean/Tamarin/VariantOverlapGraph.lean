import TamarinRuntime.VariantOverlapGraph
import Tamarin.MixedSizeGraphDecode
import Tamarin.CheckedFactoring
import Tamarin.VariantOverlapAgreement

namespace Tamarin.VariantOverlapGraph
open Whole WholeProblem FactorCheck FactorInterpretation Cancellation

/-- An observation can be followed to the same child position through
any number of shared free heads. Commutative heads have no such positions. -/
inductive Projects (x y : Tree) : Tree → Tree → Prop where
  | root : Projects x y x y
  | child {f xs ys a b} (aligned : (a,b) ∈ xs.zip ys) (next : Projects x y a b) :
      Projects x y (.app 2 f xs) (.app 2 f ys)

def Observed (inputs : Observations) (x y : Tree) : Prop :=
  ∃ e ∈ inputs, Projects x y e.1 e.2

mutual
  private theorem read_projection (a b x y : Tree) (mem : (x,y) ∈ projections a b) :
      Projects x y a b := by
    rw [projections.eq_def,List.mem_cons] at mem
    rcases mem with e | more
    · cases e; exact .root
    · cases a <;> cases b <;> try contradiction
      rename_i k f xs l g ys
      change (x,y) ∈ (if k = 2 ∧ l = 2 ∧ f = g then projectArgs xs ys else []) at more
      split at more
      · obtain ⟨rfl,rfl,rfl⟩ := ‹_ ∧ _ ∧ _›
        obtain ⟨u,v,member,d⟩ := read_projectArgs _ _ x y more
        exact .child member d
      · contradiction
  private theorem read_projectArgs (xs ys : List Tree) (x y : Tree) (mem : (x,y) ∈ projectArgs xs ys) :
      ∃ u v, (u,v) ∈ xs.zip ys ∧ Projects x y u v := by
    cases xs with
    | nil => contradiction
    | cons a as =>
      cases ys with
      | nil => contradiction
      | cons b bs =>
        rcases List.mem_append.mp mem with head | tail
        · exact ⟨a,b,List.mem_cons_self,read_projection _ _ _ _ head⟩
        · obtain ⟨u,v,h,d⟩ := read_projectArgs _ _ _ _ tail
          exact ⟨u,v,List.mem_cons_of_mem _ h,d⟩
end

private theorem in_projection_args {xs ys : List Tree} {a b x y : Tree}
    (aligned : (a,b) ∈ xs.zip ys) (mem : (x,y) ∈ projections a b) : (x,y) ∈ projectArgs xs ys := by
  induction xs generalizing ys with
  | nil => simp at aligned
  | cons l ls ih =>
    cases ys with
    | nil => simp at aligned
    | cons r rs =>
      rcases List.mem_cons.mp aligned with eq | tail
      · cases eq; exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (ih tail)

private theorem write_projection {a b x y : Tree} (h : Projects x y a b) :
    (x,y) ∈ projections a b := by
  induction h with
  | root => rw [projections.eq_def]; exact List.mem_cons_self
  | child aligned _ ih =>
    rw [projections]
    exact List.mem_cons_of_mem _ (by simpa using in_projection_args aligned ih)

private theorem eval_aligned {α} (m n : Interpretation α) {xs ys a b}
    (entry : (a,b) ∈ xs.zip ys) (eq : m.evalArgs xs = n.evalArgs ys) : m.eval a = n.eval b := by
  induction xs generalizing ys with
  | nil => simp at entry
  | cons l ls ih =>
    cases ys with
    | nil => simp at entry
    | cons r rs =>
      obtain ⟨head,tail⟩ := List.cons.inj eq
      rcases List.mem_cons.mp entry with pair | child
      · cases pair; exact head
      · exact ih child tail

private theorem Projects.eval_eq {α} (m n : Interpretation α) (apps : m.app = n.app)
    {a b x y} (path : Projects x y a b) : m.eval a = n.eval b → m.eval x = n.eval y := by
  induction path with
  | root => exact id
  | child aligned _ ih =>
    intro parent
    simp only [Interpretation.eval,apps] at parent
    exact ih (eval_aligned m n aligned ((n.free_inj _) parent))

/- Derivations remember which input pair was used at each hole. The two
members of a hole may contain wholly independent variable names. -/
mutual
  inductive Common (inputs : Observations) : Tree → Tree → Prop
    | input {a b} : Observed inputs a b → Common inputs a b
    | atom (i s) : Common inputs (.leaf 1 i s) (.leaf 1 i s)
    | app (k f) {xs ys} : CommonArgs inputs xs ys → Common inputs (.app k f xs) (.app k f ys)
  inductive CommonArgs (inputs : Observations) : List Tree → List Tree → Prop
    | nil : CommonArgs inputs [] []
    | cons {a b xs ys} : Common inputs a b → CommonArgs inputs xs ys → CommonArgs inputs (a :: xs) (b :: ys)
end

private theorem hit (inputs : Observations) (a b : Tree) :
    (index inputs).contains (key a b) = true ↔ Observed inputs a b := by
  simp only [index,Std.HashSet.contains_iff_mem,Std.HashSet.mem_ofList,List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨⟨x,y⟩,mem,eq⟩
    have le : x = a := Tree.key_injective (congrArg Prod.fst eq)
    have re : y = b := Tree.key_injective (congrArg Prod.snd eq)
    obtain ⟨e,entry,proj⟩ := List.mem_flatMap.mp mem
    exact ⟨e,entry,le ▸ re ▸ read_projection _ _ _ _ proj⟩
  · rintro ⟨e,entry,proj⟩
    exact ⟨(a,b),List.mem_flatMap.mpr ⟨e,entry,write_projection proj⟩,rfl⟩

mutual
  private theorem read_pair (inputs : Observations) (a b : Tree)
      (yes : checkPair (index inputs) a b = true) : Common inputs a b := by
    cases a with
    | leaf k i s =>
      cases b with
      | leaf l j t =>
        simp only [checkPair,Bool.or_eq_true,hit,Bool.and_eq_true,beq_iff_eq] at yes
        rcases yes with member | ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
        · exact .input member
        · exact .atom _ _
      | app => exact .input ((hit ..).mp (by simpa only [checkPair,Bool.or_false] using yes))
    | app k f xs =>
      cases b with
      | leaf => exact .input ((hit ..).mp (by simpa only [checkPair,Bool.or_false] using yes))
      | app l g ys =>
        simp only [checkPair,Bool.or_eq_true,hit,Bool.and_eq_true,beq_iff_eq] at yes
        rcases yes with member | ⟨⟨rfl,rfl⟩,ok⟩
        · exact .input member
        · exact .app _ _ (read_args _ xs ys ok)
  private theorem read_args (inputs : Observations) (xs ys : List Tree)
      (yes : matchesArgs (index inputs) xs ys = true) : CommonArgs inputs xs ys := by
    cases xs with
    | nil => cases ys <;> simp [matchesArgs] at yes; exact .nil
    | cons x xs =>
      cases ys with
      | nil => contradiction
      | cons y ys =>
        simp only [matchesArgs,Bool.and_eq_true] at yes
        obtain ⟨one,rest⟩ := yes
        exact .cons (read_pair _ x y one) (read_args _ xs ys rest)
end

mutual
  private theorem write_pair {inputs a b} (derivation : Common inputs a b) :
      checkPair (index inputs) a b = true := by
    cases derivation with
    | input obs => cases a <;> cases b <;> simp [checkPair,(hit ..).mpr obs]
    | atom => simp [checkPair]
    | app k f args => simp [checkPair,write_args args]
  private theorem write_args {inputs xs ys} (derivation : CommonArgs inputs xs ys) :
      matchesArgs (index inputs) xs ys = true := by
    cases derivation with
    | nil => rfl
    | cons a as => simp [matchesArgs,write_pair a,write_args as]
end

/-- Both successful returns and the mandatory set are specified on the
original packet. Any agreed context over paired inputs within the physical
envelope must be accepted. -/
def Structural (candidate : Kernel) : Prop := ∀ ds ns es, candidate ds ns es = true ↔
  ds.size ≤ 32768 ∧ MixedSizeGraph.GraphWithin ns es ∧ ∃ inputs a b,
    Wire.decodeProblem ds ns es = some (inputs ++ [(a,b)]) ∧ Common inputs a b

theorem runWith_iff (extra : Observations → Tree → Tree → Bool) (ds ns es) :
    runWith extra ds ns es = true ↔ ds.size ≤ 32768 ∧ MixedSizeGraph.GraphWithin ns es ∧
      ∃ inputs a b, Wire.decodeProblem ds ns es = some (inputs ++ [(a,b)]) ∧
        (Common inputs a b ∨ extra inputs a b = true) := by
  simp only [runWith,Bool.and_eq_true,decide_eq_true_eq,MixedSizeGraph.withinGraph_iff]
  constructor
  · rintro ⟨⟨size,graph⟩,ok⟩
    cases parsed : Wire.decodeProblem ds ns es with
    | none => simp [parsed] at ok
    | some raw =>
      cases rev : raw.reverse with
      | nil => simp [parsed,rev] at ok
      | cons pair rest =>
        have orig := congrArg List.reverse rev
        simp at orig
        refine ⟨size,graph,rest.reverse,pair.1,pair.2,by rw [orig],?_⟩
        simp only [parsed,rev,Option.any_some,Bool.or_eq_true] at ok
        exact ok.imp (fun h => read_pair _ _ _ h) id
  · rintro ⟨size,graph,obs,a,b,parsed,h⟩
    have yes := h.imp (fun d => write_pair d) id
    exact ⟨⟨size,graph⟩,by simpa [parsed,List.reverse_append] using yes⟩

theorem run_structural : Structural run := by
  intro ds ns es
  simpa [run] using runWith_iff (fun _ _ _ => false) ds ns es

mutual
  private theorem value_eq {α} (m n : Interpretation α) (apps : m.app = n.app)
      (atoms : m.leaf 1 = n.leaf 1) {obs} (inputs : ∀ e ∈ obs, m.eval e.1 = n.eval e.2)
      {a b} (d : Common obs a b) : m.eval a = n.eval b := by
    cases d with
    | input h =>
      obtain ⟨e,entry,proj⟩ := h
      exact proj.eval_eq m n apps (inputs e entry)
    | atom => simp [Interpretation.eval,atoms]
    | app k f args => simp only [Interpretation.eval,apps,values_eq m n apps atoms inputs args]
  private theorem values_eq {α} (m n : Interpretation α) (apps : m.app = n.app)
      (atoms : m.leaf 1 = n.leaf 1) {obs} (inputs : ∀ e ∈ obs, m.eval e.1 = n.eval e.2)
      {xs ys} (d : CommonArgs obs xs ys) : m.evalArgs xs = n.evalArgs ys := by
    cases d with
    | nil => rfl
    | cons h t => simp only [Interpretation.evalArgs,value_eq m n apps atoms inputs h,values_eq m n apps atoms inputs t]
end

open Rewriting.VariantOverlapAgreement

private def view {α} (m n : Interpretation α) (e : Tree × Tree) := (m.eval e.1, n.eval e.2)

private def image {s : Signature} (σ τ : Substitution s) (e : Equation s) : Value s × Value s :=
  (.semantic (classOf (σ.apply e.lhs)), .semantic (classOf (τ.apply e.rhs)))

private theorem rows_view {s : Signature} (c : Codec s) (σ τ : Substitution s) (p : Problem s)
    {raw} (represented : CheckedFactoring.Rows c p raw) :
    raw.map (view (model c σ) (model c τ)) = p.map (image σ τ) := by
  induction p generalizing raw with
  | nil => cases represented.layout; rfl
  | cons e p ih =>
    cases represented.layout with
    | cons l r rest =>
      have live := represented.faithful e List.mem_cons_self
      have a := (eval_layout c σ l).symm.trans (eval_encode c σ _ live.1)
      have b := (eval_layout c τ r).symm.trans (eval_encode c τ _ live.2)
      simp only [List.map_cons,view,image,Prod.mk.injEq,List.cons.injEq]
      exact ⟨⟨a,b⟩,ih ⟨rest,fun e he => represented.faithful e (List.mem_cons_of_mem _ he)⟩⟩

def equations {s : Signature} {I : Type} (ids : List I) (left right : I → Term s) (a b : Term s) :
    Problem s :=
  (ids.map fun i => ⟨left i,right i⟩) ++ [⟨a,b⟩]

private theorem implication {s : Signature} {I : Type} (c : Codec s) (ids : List I)
    (left right : I → Term s) (a b : Term s) {obs x y}
    (rep : CheckedFactoring.Rows c (equations ids left right a b) (obs ++ [(x,y)]))
    (common : Common obs x y) : Agrees left right a b := by
  intro σ τ equal
  let m := model c σ
  let n := model c τ
  have split := congrArg List.reverse (rows_view c σ τ _ rep)
  simp only [equations,List.map_append,List.map_cons,List.map_nil,List.reverse_append,List.reverse_cons,
    List.reverse_nil,List.nil_append,List.cons_append,List.cons.injEq,List.reverse_inj] at split
  obtain ⟨last,first⟩ := split
  have agree : ∀ e ∈ obs, m.eval e.1 = n.eval e.2 := by
    intro e h
    have contains := List.mem_map_of_mem (f := view m n) h
    rw [first] at contains
    obtain ⟨entry,member,eq⟩ := List.mem_map.mp contains
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
    exact (congrArg Prod.fst eq).symm.trans ((congrArg Value.semantic (Quotient.sound (equal i))).trans (congrArg Prod.snd eq))
  have value := value_eq m n rfl rfl agree common
  exact Quotient.exact (Value.semantic.inj (((congrArg Prod.fst last).symm.trans value).trans (congrArg Prod.snd last)))

/-- Each true verdict guarantees agreement under independent substitutions.
All physically bounded derivable contexts must complete; other true verdicts
are permitted when the source-level agreement is proved. -/
structure Correct (candidate : Kernel) : Prop where
  malformed : ∀ ds ns es, Wire.decodeProblem ds ns es = none → candidate ds ns es = false
  semantic : ∀ {s : Signature} {I : Type} (c : Codec s) (ids : List I) (left right : I → Term s)
    (a b : Term s) ds ns es raw, Wire.decodeProblem ds ns es = some raw →
    CheckedFactoring.Rows c (equations ids left right a b) raw → candidate ds ns es = true → Agrees left right a b
  completes : ∀ ds ns es obs a b, ds.size ≤ 32768 → MixedSizeGraph.GraphWithin ns es →
    Wire.decodeProblem ds ns es = some (obs ++ [(a,b)]) → Common obs a b → candidate ds ns es = true

theorem run_correct : Correct run where
  malformed := by
    intro ds ns es bad
    cases h : run ds ns es with
    | false => rfl
    | true => obtain ⟨_,_,_,_,_,read,_⟩ := (run_structural ..).mp h; simp [bad] at read
  semantic := by
    intro s I c ids left right a b ds ns es raw decoded rep yes
    obtain ⟨_,_,obs,x,y,read,d⟩ := (run_structural ..).mp yes
    cases decoded.symm.trans read
    exact implication c ids left right a b rep d
  completes := fun _ _ _ obs a b sz g read d => (run_structural ..).mpr ⟨sz,g,obs,a,b,read,d⟩

end Tamarin.VariantOverlapGraph
