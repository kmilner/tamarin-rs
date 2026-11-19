import Tamarin.DenseOpening
import TamarinRuntime

namespace Tamarin.FactoredUnificationTests
open FactoredUnification

private def x : Variable := ⟨0, .msg⟩
private def y : Variable := ⟨1, .msg⟩
private def z : Variable := ⟨2, .msg⟩

variable {sig : Signature}

private def residual : Problem sig := [⟨.var z, .var z⟩]
private def original : Problem sig := ⟨.var x, .var y⟩ :: residual
private def factor : Substitution sig := .binding x (.var y) (.var y)
private def arm : Substitution sig := .binding z (.var y) (.var y)

private theorem trace : Trace (original (sig := sig)) .identity residual factor :=
  .bind x (.var y) (.var y) (by change x ≠ y; decide) residual .identity

private theorem observes (v : Variable) : (residual (sig := sig)).Occurs v ↔ v = z := by
  simp [residual, Problem.Occurs, Term.Occurs]

/-- z ↦ y represents every solution of z = z when y is available as a witness. -/
private theorem residual_correct : (Outcome.complete [arm (sig := sig)]).CorrectIn residual [] := by
  constructor
  · constructor
    · intro σ _ e he
      obtain rfl : e = ⟨.var z, .var z⟩ := List.mem_singleton.mp he
      exact .refl _
    · intro ρ _
      refine ⟨arm, List.mem_singleton_self _, Substitution.binding y (ρ.image z) (ρ.sorted z), ?_⟩
      intro v hv
      obtain rfl := (observes v).mp hv
      exact .refl _
  · intro σ hσ v hv
    obtain rfl : σ = arm := List.mem_singleton.mp hσ
    exact Substitution.binding_image_other _ _ _ _ (fun hz => hv ((observes v).mpr hz))
  · intro _ _ _ _ _ _ _ hin
    exact List.not_mem_nil hin

/-- The factor retains y after y has disappeared from the residual. If the
residual picks y as its witness for z, the only composed arm forces y = z.
The original solution x ↦ y leaves z independent. -/
example : Factoring (original (sig := sig)) residual factor ∧
    Scope (original (sig := sig)).Occurs residual (factor (sig := sig)) ∧
    (Outcome.complete [arm (sig := sig)]).CorrectIn residual [] ∧
    ¬ Protected original residual (factor (sig := sig)) [] ∧
    ¬ Covers original [arm.compose (factor (sig := sig))] := by
  refine ⟨trace.factoring, trace.original_scope, residual_correct, ?_, ?_⟩
  · intro protectedVars
    have := protectedVars x ⟨_, List.mem_cons_self, Or.inl rfl⟩ y rfl
      (fun h => (by decide : y ≠ z) ((observes y).mp h))
    exact List.not_mem_nil this
  · intro covers
    have solves : original.Solves (factor (sig := sig)) := by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact .refl _
      · obtain rfl : e = ⟨.var z, .var z⟩ := List.mem_singleton.mp he
        exact .refl _
    obtain ⟨σ, hσ, δ, agrees⟩ := covers factor solves
    obtain rfl : σ = arm.compose factor := List.mem_singleton.mp hσ
    have hy : EquivB (.var y) (δ.image y) :=
      agrees y ⟨_, List.mem_cons_self, Or.inr rfl⟩
    have hz : EquivB (.var z) (δ.image y) :=
      agrees z ⟨⟨.var z, .var z⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), Or.inl rfl⟩
    exact (by decide : y ≠ z) (((hy.trans hz.symm).occurs_iff y).mp rfl)

-- Free and AC heads share an ID. The graph includes two uses of the same
-- child, an independent atom, and an incompatible variable sort.
private def decls : Array UInt64 := #[2,7,2,2,2,2, 4,7,2,2,2,2]
private def graph : Array (Array UInt64) := #[
  #[0,0,2], #[0,1,2], #[1,0,2], #[1,1,2],
  #[2,7,0,0], #[2,7,1,1], #[4,7,0,2], #[4,7,1,2], #[4,7,1,3], #[0,3,1]]
private def accepts := FactorCheck.run decls graph

-- Expose the two identical free children, bind x = y once and propagate it
-- through AC. Swapping or repeating an entire residual equation is harmless.
#guard accepts #[4,5,6,8] #[0,1] #[8,7,7,8]
#guard !accepts #[4,5,6,8] #[0,1] #[]
#guard !accepts #[4,5,6,8] #[0,1] #[7,8,2,3]
#guard !accepts #[4,5,6,8] #[0,1] #[6,8]
#guard !accepts #[4,5] #[0,1,0,1] #[]
#guard !accepts #[0,1,1,0] #[0,1,1,0] #[]
#guard !accepts #[6,7] #[0,1] #[]
#guard !accepts #[0,6] #[0,6] #[]
#guard !accepts #[9,1] #[9,1] #[]
#guard !accepts #[2,3] #[2,3] #[]

-- Invalid indices in each root list and malformed rows invalidate the whole
-- certificate, including malformed rows shared by reflexive roots.
#guard !accepts #[0,20] #[] #[]
#guard !accepts #[0,1] #[0,20] #[]
#guard !accepts #[0,1] #[] #[20,1]
#guard !FactorCheck.run decls (graph.push #[2,7,10,10]) #[10,10] #[] #[]
#guard !FactorCheck.run decls (graph.push #[2,7,1]) #[10,10] #[] #[]
#guard !FactorCheck.run decls (graph.push #[4,99,1,1]) #[] #[] #[]

-- Exhaust the empty and singleton systems on two Msg variables and two
-- distinct rigid atoms. Independently evaluate each accepted certificate
-- under all four assignments of those atoms to the variables.
private def systems : List (List (Nat × Nat)) :=
  [] :: (List.range 4).flatMap fun i => (List.range 4).map fun j => [(i,j)]

private def roots (qs : List (Nat × Nat)) : Array UInt64 :=
  (qs.flatMap fun (i,j) => [i.toUInt64, j.toUInt64]).toArray

private def holds (env : Nat → Bool) (qs : List (Nat × Nat)) : Bool :=
  qs.all fun (i,j) => env i == env j

private def factorPreserves (p bs q : List (Nat × Nat)) (a b : Bool) : Bool :=
  let env := fun i => match i with | 0 => a | 1 => b | 2 => false | _ => true
  let bound := fun i => match bs with
    | [(key,rhs)] => if i == key then env rhs else env i
    | _ => env i
  (!(holds env q) || holds bound p) &&
    (!(holds env p) || (holds env q && holds env bs))

private def finiteAudit : Bool :=
  let ns := graph.extract 0 4
  systems.all fun p => systems.all fun bs => systems.all fun q =>
    !FactorCheck.run #[] ns (roots p) (roots bs) (roots q) ||
      [false,true].all fun a => [false,true].all fun b => factorPreserves p bs q a b

#guard finiteAudit

namespace Production
open ACSystem Homogeneous Whole WholeProblem FactoredAC

-- x = y and 2x = 3z. Factoring changes a variable occurring twice in the
-- matrix. The wire shares the flat triple z + z + z across both systems.
private def signature : Signature where
  FreeSym := Empty
  CSym := Empty
  ACSym := Unit
  Atom := Empty
  arity := Empty.elim
  inputSort := fun f => nomatch f
  outputSort := Empty.elim
  cSort := Empty.elim
  acSort := fun _ => .msg
  atomSort := Empty.elim

private def plus : signature.ACSym := ()
private def rows : List ACSystem.Row := [⟨⟨y,[y]⟩, ⟨z,[z,z]⟩⟩]
private def request : Request signature :=
  ⟨⟨.var x, .var y⟩ :: problem plus [⟨⟨x,[x]⟩, ⟨z,[z,z]⟩⟩], [⟨100,.msg⟩]⟩

private def unusedNames : Names Empty := ⟨Empty.elim, fun _ => none⟩
private def codec : Codec signature where
  vars := ⟨fun v => if v = y then 0 else if v = z then 1 else 2,
    fun i => if i = 0 then some y else if i = 1 then some z else if i = 2 then some x else none⟩
  atoms := unusedNames
  frees := unusedNames
  comms := unusedNames
  acs := ⟨fun _ => 7, fun i => if i = 7 then some () else none⟩

private def packet : Input signature where
  codec := codec
  decls := #[4,7,2,2,2,2]
  nodes := #[#[0,2,2], #[0,0,2], #[0,1,2], #[4,7,0,0], #[4,7,1,1], #[4,7,2,2,2]]
  original := #[0,1,3,5]
  bindings := #[0,1]
  residual := #[4,5]

private theorem wire : packet.Represents request.problem factor (problem plus rows) := by
  intro ds ts os bs rs hd ht ho hb hr
  have decoded : declarations packet.decls.toList = some [⟨4,7,2,[2,2]⟩] := by
    change declarations [4,7,2,2,2,2] = _
    simp [declarations, guard]
  rw [decoded] at hd
  cases hd
  let xr := encode codec (Term.var x)
  let yr := encode codec (Term.var y)
  let zr := encode codec (Term.var z)
  let twice (t : Tree) := Tree.app 4 7 [t,t]
  let three := Tree.app 4 7 [zr,zr,zr]
  let trees := #[xr,yr,zr,twice xr,twice yr,three]
  have nodes : decodeNodes [⟨4,7,2,[2,2]⟩] packet.nodes = some trees := by
    apply beq_iff_eq.mp
    dsimp only [trees, xr,yr,zr, twice, three]
    decide +kernel
  rw [nodes] at ht
  replace ht := Option.some.inj ht
  subst ts
  have src : readEquations trees packet.original.toList = some [(xr,yr),(twice xr,three)] := by rfl
  have sub : readEquations trees packet.bindings.toList = some [(xr,yr)] := by rfl
  have dst : readEquations trees packet.residual.toList = some [(twice yr,three)] := by rfl
  rw [src] at ho
  rw [sub] at hb
  rw [dst] at hr
  replace ho := Option.some.inj ho
  replace hb := Option.some.inj hb
  replace hr := Option.some.inj hr
  subst os bs rs
  have flat := Layout.flatten 7 [zr] [zr,zr] []
  refine ⟨⟨.cons (.refl _) (.refl _) (.cons (.refl _) flat .nil), ?_⟩,
    ⟨.cons (.refl _) flat .nil, ?_⟩, [x], ⟨.refl _, ?_⟩, factor.outside⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp he
      exact ⟨⟨rfl,rfl,rfl⟩, ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  · intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨⟨rfl,rfl,rfl⟩, ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  · intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨rfl,rfl⟩

private def frame : Frame plus rows 2 where
  names := fun i => if i = 0 then y else z
  index := fun v => if v = y then some 0 else if v = z then some 1 else none
  inverse := by decide
  live := by
    intro v hv
    have h : v = y ∨ v = z := by simpa [rows, variables, Side.vars] using hv
    rcases h with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  used := by decide
  sorts := by decide

private def answer : Answers := #[#[#[0,0,0], #[0,0]]]
private def witness (_ : UInt64) : Variable := ⟨3,.msg⟩

-- The two exports return a nonempty arm whose five entries all denote one
-- witness. Only slot zero is used, so a locally constant slot map suffices.
private theorem accepted : FactoredAC.Result request factor frame witness answer := by
  have production : GraphUnification.Checked Executable.checkFactors Executable.graphHomogeneousUnify :=
    GraphUnification.checked_correct FactorCheck.run_correct GraphUnification.run_correct
  refine production request factor plus rows packet wire (by decide +kernel) 2 frame (by decide)
    answer (by decide +kernel) witness ?_ ?_ ?_
  · intro i hi j hj _
    have zero : slots answer = [0,0,0,0,0] := rfl
    have a : i = 0 := by simpa [zero] using hi
    have b : j = 0 := by simpa [zero] using hj
    exact a.trans b.symm
  · intro _ _; rfl
  · intro j _
    change (⟨3,.msg⟩ : Variable) ∉ _
    decide

-- Thus some ordinary substitution corresponding to the single returned arm
-- covers every original solution after composition with x ↦ y.
example : ∃ σ : Substitution signature,
    Represents frame witness #[#[0,0,0], #[0,0]] σ ∧
    CompleteSet request.problem [σ.compose factor] := by
  obtain ⟨pairs, packetEq, represents, complete, _⟩ := accepted
  have one : pairs.map Prod.fst = [#[#[0,0,0], #[0,0]]] := by
    simpa [answer] using (congrArg Array.toList packetEq).symm
  cases pairs with
  | nil => contradiction
  | cons p ps =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at one
    obtain ⟨hp,rfl⟩ := one
    exact ⟨p.2, hp ▸ (represents p (List.mem_singleton_self _)).1, complete⟩

private def projected : Answers := #[#[#[0,0,0,0], #[1,0,0]]]

private theorem projected_ok : ProjectedBindings.Denotes request factor frame witness
    .identity projected := by
  have h : ProjectedBindings.Checked Executable.checkFactors Executable.graphHomogeneousUnify
      Executable.projectAnswers := ProjectedBindings.checked_correct
    (GraphUnification.checked_correct FactorCheck.run_correct GraphUnification.run_correct)
    AnswerProjection.project_correct
  apply h request factor plus rows packet wire (by decide +kernel) 2 frame (by decide)
    answer (by decide +kernel) projected (by decide +kernel) witness .identity
  · intro i hi j hj _
    have zero : ProjectedBindings.ordinals projected = [0,0,0,0,0] := rfl
    have a : i = 0 := by simpa [zero] using hi
    have b : j = 0 := by simpa [zero] using hj
    exact a.trans b.symm
  · intro _ _; rfl
  · intro j _
    change (⟨3,.msg⟩ : Variable) ∉ _
    decide

-- Compute the exact emitted rows and obtain completeness for the original equations.
private def three := (Side.mk (witness 0) [witness 0, witness 0]).term plus
private def two := (Side.mk (witness 0) [witness 0]).term plus
example : ∃ b : FreshAnswer signature,
    (DenseOpening.close [x,y,z] factor b).bindings = [(x,three),(y,three),(z,two)] ∧
    CompleteSet request.problem [(FactoredAnswer.readBindings b).compose factor] := by
  obtain ⟨bs, decoded, complete, _⟩ := projected_ok
  have known : projected.toList.mapM (ProjectedBindings.readArm frame.names plus witness .identity) =
      some [[(y,three),(z,two)]] := rfl
  have h := Option.some.inj (decoded.symm.trans known)
  cases bs with
  | nil => contradiction
  | cons b bs =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at h
    obtain ⟨hb,rfl⟩ := h
    refine ⟨b, ?_, complete⟩
    cases b with
    | mk bindings sorted =>
      change bindings = _ at hb
      subst bindings
      rfl

end Production
end Tamarin.FactoredUnificationTests
