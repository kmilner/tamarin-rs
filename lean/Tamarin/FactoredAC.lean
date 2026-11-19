import Tamarin.CheckedFactoring
import Tamarin.FactoredAnswer
import Tamarin.HomogeneousContract

/-! Compose a checked free factor and a homogeneous AC solver at the level of
the original sorted query. The residual graph and the coefficient matrix must
represent the same rows. A residual witness is shared across the entire arm. -/
namespace Tamarin.FactoredAC
open ACSystem Homogeneous
variable {sig : Signature}

abbrev Branch (sig : Signature) := Arm × Substitution sig

/-- On ordinary decoded arms, remove any chosen sequence of isolated aliases
before composing with the free factor. Empty order preserves all bindings. -/
def prepared (p : Problem sig) (θ σ : Substitution sig) (order : List Variable) :=
  order.foldl (FactoredAnswer.omitIfIsolated (FactoredAnswer.liveKeys p θ)) σ

private theorem prepared_equivalent (p : Problem sig) (θ σ : Substitution sig)
    (order : List Variable) :
    FactoredAnswer.ArmEquivalent (FactoredAnswer.live p θ) σ (prepared p θ σ order) := by
  have seen : (· ∈ FactoredAnswer.liveKeys p θ) = FactoredAnswer.live p θ :=
    funext fun _ => propext FactoredAnswer.mem_liveKeys
  exact seen ▸ FactoredAnswer.omit_many (FactoredAnswer.liveKeys p θ) order σ

/-- The numeric arms and the original answer set refer to the same list of
branches, preserving multiplicity and even the distinction between zero arms
and one identity arm. The reference result is unconditional. A materializer
can instead supply its own finite rows, order of erasures and fresh names. -/
def Result (r : Request sig) (θ : Substitution sig) {f : sig.ACSym} {rows : List ACSystem.Row}
    {n : Nat} (fr : Frame f rows n) (w : UInt64 → Variable) (out : Answers) : Prop :=
  ∃ pairs : List (Branch sig), out = (pairs.map Prod.fst).toArray ∧
    (∀ b ∈ pairs, Represents fr w b.1 b.2 ∧ DomainRestricted (problem f rows) b.2) ∧
    CompleteSet r.problem (pairs.map fun b => b.2.compose θ) ∧
    (Outcome.complete (pairs.map fun b => FreshAnswer.freshen r.problem r.avoid (b.2.compose θ))).CorrectIn
      r.problem r.avoid ∧
    ∀ (order : Arm → List Variable) (packet : Arm → FreshAnswer sig),
      let composed := fun b : Branch sig => (prepared r.problem θ b.2 (order b.1)).compose θ
      ∀ a : (b : Branch sig) → CallerFreshening.Allocation (CallerFreshening.sources r.problem (composed b)),
      (∀ b ∈ pairs, FactoredAnswer.Stores r.problem (composed b) (packet b.1) (a b)) →
      (∀ b ∈ pairs, CallerFreshening.Avoids r (composed b) (a b)) →
      (Outcome.complete (out.toList.map fun arm => FactoredAnswer.readBindings (packet arm))).CorrectIn
        r.problem r.avoid

/-- Exactly the witness words read by the caller, including words shared
between rows or repeated within a single image. -/
def slots (out : Answers) : List UInt64 :=
  out.toList.flatMap fun arm => arm.toList.flatMap Array.toList

theorem extend_slots (used : List UInt64) (avoid : List Variable)
    (sort : SortId) (w : UInt64 → Variable)
    (injective : ∀ i ∈ used, ∀ j ∈ used, w i = w j → i = j)
    (sorted : ∀ i ∈ used, (w i).sort = sort) (fresh : ∀ i ∈ used, w i ∉ avoid) :
    ∃ v : UInt64 → Variable, (∀ i ∈ used, v i = w i) ∧ Function.Injective v ∧
      (∀ i, (v i).sort = sort) ∧ (∀ i, v i ∉ avoid) := by
  let occupied := used.map w ++ avoid
  let extra (i : UInt64) : Variable := ⟨VariablePermutation.freshBound occupied + i.toNat, sort⟩
  have outside (i) : extra i ∉ occupied := by
    intro hm
    have h := VariablePermutation.lt_freshBound occupied (extra i) hm
    change VariablePermutation.freshBound occupied + i.toNat < VariablePermutation.freshBound occupied at h
    omega
  have present (i) (hi : i ∈ used) : w i ∈ occupied := List.mem_append_left _ (List.mem_map_of_mem hi)
  refine ⟨fun i => if i ∈ used then w i else extra i, fun i h => ite_eq_left h, ?_, ?_, ?_⟩
  · intro i j h
    dsimp only at h
    split at h <;> split at h
    next hi hj => exact injective i hi j hj h
    next hi _ => exact False.elim (outside j (h ▸ present i hi))
    next _ hj => exact False.elim (outside i (h.symm ▸ present j hj))
    next =>
      have ids := congrArg Variable.id h
      exact UInt64.toNat_inj.mp (Nat.add_left_cancel (show
        VariablePermutation.freshBound occupied + i.toNat = _ from ids))
  · intro i
    dsimp only
    split
    next hi => exact sorted i hi
    next => rfl
  · intro i
    dsimp only
    split
    next hi => exact fresh i hi
    next => exact fun h => outside i (List.mem_append_right _ h)

private theorem Result.congr_slots {r : Request sig} {θ : Substitution sig} {f : sig.ACSym}
    {rows : List ACSystem.Row} {n : Nat} {fr : Frame f rows n} {out : Answers} {v w : UInt64 → Variable}
    (h : Result r θ fr v out) (same : ∀ j ∈ slots out, v j = w j) : Result r θ fr w out := by
  obtain ⟨pairs, packet, rep, rest⟩ := h
  refine ⟨pairs, packet, ?_, rest⟩
  intro b hb
  obtain ⟨⟨size, binding⟩, domain⟩ := rep b hb
  have arm : b.1 ∈ out.toList := by rw [packet, List.toList_toArray]; exact List.mem_map_of_mem hb
  refine ⟨⟨size, ?_⟩, domain⟩
  intro i
  obtain ⟨x, xs, decoded, image⟩ := binding i
  have index : i.val < b.1.size := size ▸ i.isLt
  have row : b.1[i.val] ∈ b.1.toList := by simp
  have names : (b.1[i.val].toList.map v) = b.1[i.val].toList.map w := by
    apply List.map_congr_left
    intro j hj
    exact same j (List.mem_flatMap.mpr ⟨b.1, arm, List.mem_flatMap.mpr ⟨_, row, hj⟩⟩)
  refine ⟨x, xs, ?_, image⟩
  simpa only [Array.getElem?_eq_getElem index, Option.map_some, names] using decoded

/-- The matrix can use any column order. Only actual multiplicities and a
faithful column inventory are required. The intermediate mathematical witness
names must avoid every variable read by the factor on an original input. -/
theorem of_factoring {solve} (kernel : Homogeneous.Correct solve) (r : Request sig)
    (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64) (fr : Frame f rows n.toNat)
    (θ : Substitution sig) (fact : FactoredUnification.Factoring r.problem (problem f rows) θ)
    (m : Matrix) (matrix : m.toList = matrixWords fr.names rows)
    (fits : ∀ row ∈ rows, ∀ s ∈ [row.lhs, row.rhs], ∀ i, s.vars.count (fr.names i) < 2^64)
    (out : Answers) (ran : solve n m = some out) (w : UInt64 → Variable)
    (inj : Function.Injective w) (sorted : ∀ j, (w j).sort = sig.acSort f)
    (fresh : ∀ j, w j ∉ variables rows ++ FactoredAnswer.liveKeys r.problem θ) :
    Result r θ fr w out := by
  have read := read_matrixWords fr.names rows fr.live fits
  rw [← matrix] at read
  obtain ⟨pairs, eq, rep, residual⟩ := kernel.semantic f rows _ n fr m read out ran w inj sorted fresh
  have complete := FactoredUnification.lift_complete fact residual
    (fun v hv z hz _ => FactoredAnswer.mem_liveKeys.mpr ⟨v,hv,hz⟩)
  have full : CompleteSet r.problem (pairs.map fun b => b.2.compose θ) := by
    simpa only [List.map_map, Function.comp_def] using complete
  refine ⟨pairs, eq, fun b hb => ⟨rep b hb, residual.domain b.2 (List.mem_map_of_mem hb)⟩, full, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using FreshAnswer.freshen_correct r _ full
  · intro order packet
    dsimp only
    intro a entries avoids
    rw [eq, List.toList_toArray, List.map_map]
    exact FactoredAnswer.materialized_complete r θ pairs Prod.snd
      (fun b => prepared r.problem θ b.2 (order b.1)) (fun b => packet b.1) a
      (fun b _ => prepared_equivalent r.problem θ b.2 _) entries avoids full

/-- Lift a completed matrix using only the finite witness slots read by its consumer. -/
theorem of_factoring_slots {solve} (kernel : Homogeneous.Correct solve) (r : Request sig)
    (f : sig.ACSym) (rows : List ACSystem.Row) (n : UInt64) (fr : Frame f rows n.toNat)
    (θ : Substitution sig) (fact : FactoredUnification.Factoring r.problem (problem f rows) θ)
    (m : Matrix) (matrix : m.toList = matrixWords fr.names rows)
    (fits : ∀ row ∈ rows, ∀ side ∈ [row.lhs,row.rhs], ∀ i, side.vars.count (fr.names i) < 2^64)
    (out : Answers) (ran : solve n m = some out) (w : UInt64 → Variable)
    (inj : ∀ i ∈ slots out, ∀ j ∈ slots out, w i = w j → i = j)
    (sorted : ∀ j ∈ slots out, (w j).sort = sig.acSort f)
    (fresh : ∀ j ∈ slots out, w j ∉ variables rows ++ FactoredAnswer.liveKeys r.problem θ) :
    Result r θ fr w out := by
  obtain ⟨v, agree, vi, vs, vf⟩ := extend_slots (slots out) _ _ w inj sorted fresh
  exact (of_factoring kernel r f rows n fr θ fact m matrix fits out ran v vi vs vf).congr_slots agree

/-- All root arrays address the same node graph. Each is interpreted against
the original equations, the proposed factor, or the *same* AC rows used to
count the matrix. These conditions concern only identities and term layout. -/
structure Input (sig : Signature) where
  codec : WholeProblem.Codec sig
  decls : Array UInt64
  nodes : Array (Array UInt64)
  original : Array UInt64
  bindings : Array UInt64
  residual : Array UInt64

def Input.Represents (g : Input sig) (p : Problem sig) (θ : Substitution sig) (q : Problem sig) : Prop :=
  ∀ ds trees os bs rs,
    Whole.declarations g.decls.toList = some ds → Whole.decodeNodes ds g.nodes = some trees →
    Whole.readEquations trees g.original.toList = some os → Whole.readEquations trees g.bindings.toList = some bs →
    Whole.readEquations trees g.residual.toList = some rs →
    CheckedFactoring.Rows g.codec p os ∧ CheckedFactoring.Rows g.codec q rs ∧
      ∃ keys : List Variable, CheckedFactoring.Rows g.codec (CheckedFactoring.bindingProblem θ keys) bs ∧
        ∀ v, v ∉ keys → θ.image v = .var v

theorem Input.checked_factor (g : Input sig) {p q : Problem sig} {θ : Substitution sig}
    {check} (checked : FactorCheck.Correct check) (represents : g.Represents p θ q)
    (accepted : check g.decls g.nodes g.original g.bindings g.residual = true) :
    ∃ rs, Whole.Wire.decodeProblem g.decls g.nodes g.residual = some rs ∧
      CheckedFactoring.Rows g.codec q rs ∧ FactoredUnification.Factoring p q θ := by
  obtain ⟨decl, trees, os, bs, rs, hd, ht, ho, hb, hr, valid⟩ := checked _ _ _ _ _ accepted
  obtain ⟨original, residual, keys, encoded, outside⟩ := represents _ _ _ _ _ hd ht ho hb hr
  have bindings := CheckedFactoring.Bindings.of_rows original.faithful keys encoded outside
  exact ⟨rs, by simp [Whole.Wire.decodeProblem, hd, ht, hr], residual,
    CheckedFactoring.factoring g.codec valid original bindings residual⟩

/-- A matrix that represents the residual equations lifts through the checked factor
to the original problem. The graph solver derives the matrix premise from the wire roots. -/
def Correct (check : FactorCheck.Kernel) (solve : UInt64 → Matrix → Option Answers) : Prop :=
  ∀ {s : Signature} (r : Request s) (θ : Substitution s) (f : s.ACSym) (rows : List ACSystem.Row)
    (g : Input s) (_layout : g.Represents r.problem θ (problem f rows))
    (_accept : check g.decls g.nodes g.original g.bindings g.residual = true)
    (n : UInt64) (fr : Frame f rows n.toNat) (m : Matrix) (_matrix : m.toList = matrixWords fr.names rows)
    (_fits : ∀ row ∈ rows, ∀ side ∈ [row.lhs, row.rhs], ∀ i, side.vars.count (fr.names i) < 2^64)
    (out : Answers) (_ran : solve n m = some out) (w : UInt64 → Variable)
    (_inj : ∀ i ∈ slots out, ∀ j ∈ slots out, w i = w j → i = j)
    (_sorted : ∀ j ∈ slots out, (w j).sort = s.acSort f)
    (_fresh : ∀ j ∈ slots out, w j ∉ variables rows ++ FactoredAnswer.liveKeys r.problem θ),
    Result r θ fr w out

theorem correct {check solve} (checked : FactorCheck.Correct check) (matrix : Homogeneous.Correct solve) :
    Correct check solve := by
  intro s r θ f rows g represents accepted n fr m hm fits out ran w inj sorted fresh
  obtain ⟨_, _, _, fact⟩ := g.checked_factor checked represents accepted
  exact of_factoring_slots matrix r f rows n fr θ fact m hm fits out ran w inj sorted fresh

/-- The graph solver handles residual identities and closed clashes when the matrix
solver declines. Its completed answers also lift to the original request. -/
def GraphCorrect (check : FactorCheck.Kernel) (solve : WholeProblem.Kernel) : Prop :=
  ∀ {s : Signature} (r : Request s) (θ : Substitution s) (q : Problem s) (g : Input s),
    g.Represents r.problem θ q → check g.decls g.nodes g.original g.bindings g.residual = true →
    ∀ arms, WholeProblem.reply (solve g.decls g.nodes g.residual) = some (.complete arms) →
      (Outcome.complete (arms.map fun σ => FreshAnswer.freshen r.problem r.avoid (σ.compose θ))).CorrectIn
        r.problem r.avoid

theorem graph_correct {check solve} (checked : FactorCheck.Correct check) (graph : WholeProblem.Correct solve) :
    GraphCorrect check solve := by
  intro s r θ q g layout accepted arms ran
  obtain ⟨rs, decoded, rows, fact⟩ := g.checked_factor checked layout accepted
  obtain ⟨out, packet, hc, _⟩ := graph.valid g.codec q (FactoredAnswer.liveKeys r.problem θ)
    g.decls g.nodes g.residual rs decoded rows.layout rows.faithful
  cases Option.some.inj (packet.symm.trans ran)
  have complete := FactoredUnification.lift_complete fact hc
    (fun v hv z hz _ => FactoredAnswer.mem_liveKeys.mpr ⟨v,hv,hz⟩)
  simpa only [List.map_map, Function.comp_def] using FreshAnswer.freshen_correct r _ complete

end Tamarin.FactoredAC
