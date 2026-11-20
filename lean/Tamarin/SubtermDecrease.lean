import Tamarin.MixedConstructorRows
import Tamarin.SymbolWeight

/-! A relative termination certificate for user equations mixed with an existing
presentation. A projection strictly decreases every positive operator weight.
For a ground definition the head may have a higher dependency level than every
operator in the result, even when that result is larger or still reducible. -/
namespace Tamarin.SubtermDecrease
open Rewriting ConstructorVariants MixedUnification SymbolWeight
variable {s : Signature}

/-- Dropping the root exposes its arguments and their descendants. -/
def Proper (r : Equation s) : Prop :=
  r.rhs ∈ (subterms r.lhs).tail

private theorem projection {u t : Term s} (w : Head s → Nat) (pos : ∀ h, 0 < w h) :
    u ∈ (subterms t).tail →
      rank w u < rank w t ∧ u.variables.Sublist t.variables := by
  have descend {c t : Term s} (hit : u ∈ subterms c)
      (ih : u ∈ (subterms c).tail → rank w u < rank w c ∧ u.variables.Sublist c.variables)
      (child : rank w c < rank w t) (vars : c.variables.Sublist t.variables) :
      rank w u < rank w t ∧ u.variables.Sublist t.variables := by
    have cases' : u = c ∨ u ∈ (subterms c).tail := by cases c <;> simpa [subterms] using hit
    rcases cases' with rfl | sub
    · exact ⟨child,vars⟩
    · have ⟨lt,le⟩ := ih sub; exact ⟨Nat.lt_trans lt child,le.trans vars⟩
  induction t with
  | var | atom => simp [subterms]
  | free f xs ih =>
    intro sub
    obtain ⟨l,hl,hit⟩ := List.mem_flatten.mp sub
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    have child : rank w (xs i) < rank w (.free f xs) := by
      change _ < (List.ofFn (fun j => rank w (xs j))).sum + w (.free f)
      have := FiniteOccurs.le_sum _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩ : rank w (xs i) ∈ List.ofFn (fun j => rank w (xs j)))
      have := pos (.free f); omega
    have vars : (xs i).variables.Sublist (Term.free f xs).variables :=
      List.sublist_flatten_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact descend hit (ih i) child vars
  | comm f a b ia ib | ac f a b ia ib =>
    intro sub
    rcases List.mem_append.mp sub with hit | hit
    · apply descend hit ia _ (List.sublist_append_left _ _)
      change _ < rank w a + rank w b + w _
      first | have := pos (.comm f); omega | have := pos (.ac f); omega
    · apply descend hit ib _ (List.sublist_append_right _ _)
      change _ < rank w a + rank w b + w _
      first | have := pos (.comm f); omega | have := pos (.ac f); omega

/-- Use the total weight of all right sides as a strict coefficient bound. -/
def radix (base : Head s → Nat) (rs : Problem s) : Nat := 1 + (rs.map fun r => rank base r.rhs).sum

def weights (base : Head s → Nat) (rs : Problem s) (level : Head s → Nat) (h : Head s) : Nat :=
  base h * radix base rs ^ level h

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private instance : BEq (Head s) := ⟨ConstructorRows.headEq⟩

/-- Propagate tiers backwards from the heads in ground results. A ground row
already oriented at level zero needs no additional tier. A dependency path
in an acyclic graph traverses at most one edge per ground definition; the same
bound stops proposal on a cycle. Acceptance independently checks the result. -/
def inferLevel (base : Head s → Nat) (rs : Problem s) : Head s → Nat :=
  let deps := rs.filterMap fun r =>
    if r.rhs.variables.isEmpty && !(subterms r.lhs).tail.contains r.rhs then
      some (head r.lhs, (subterms r.rhs).map head, decide (rank base r.rhs < rank base r.lhs))
    else none
  let update (levels : List (Head s × Nat)) (row : Head s × List (Head s) × Bool) :=
    let (h, calls, baseOriented) := row
    let depth := calls.foldl (fun n c => max n ((levels.lookup c).getD 0)) 0
    let needed := if depth == 0 && baseOriented then 0 else depth + 1
    if needed ≤ (levels.lookup h).getD 0 then levels
    else (h,needed) :: levels.eraseP (fun entry => entry.1 == h)
  let levels := Nat.repeat (fun levels => deps.foldl update levels) deps.length []
  fun h => (levels.lookup h).getD 0

def defaultWeight (base : Head s → Nat) (rs : Problem s) : Head s → Nat :=
  weights base rs (inferLevel base rs)

/-- Symbolic rank counts every nonvariable occurrence, including atoms.
Cancel equal occurrences on the two sides before choosing a weight to raise. -/
private def residual (r : Equation s) : List (Head s) × List (Head s) :=
  let symbols (t : Term s) := (subterms t).filterMap fun
    | .var _ => none
    | u => some (head u)
  let lhs := symbols r.lhs
  let rhs := symbols r.rhs
  (rhs.foldl List.erase lhs, lhs.foldl List.erase rhs)

private def relax (base : Head s → Nat) (rs : Problem s) : Head s → Nat :=
  let read (ws : List (Head s × Nat)) (h : Head s) := (ws.lookup h).getD (base h)
  let constraints := rs.map residual
  let update (ws : List (Head s × Nat)) (row : List (Head s) × List (Head s)) :=
    match row.1 with
    | [] => ws
    | pivot :: _ =>
      let left := (row.1.map (read ws)).sum
      let right := (row.2.map (read ws)).sum
      if right < left then ws
      else (pivot, read ws pivot + (right + 1 - left)) :: ws.eraseP (fun e => e.1 == pivot)
  let rec passes : Nat → List (Head s × Nat) → List (Head s × Nat)
    | 0, ws => ws
    | n+1, ws =>
      let next := constraints.foldl update ws
      if next == ws then ws else passes n next
  read (passes constraints.length [])

/-- Try the supplied weighting and the ground dependency tiers first. If
neither suffices, relax the residual strict inequalities for at most one
pass per rule. Cycles and inconsistent choices can leave an inequality
unsatisfied; the caller checks the proposed weights against the full table. -/
def proposeWeight (base : Head s → Nat) (rs : Problem s) : Head s → Nat :=
  if decreasing base rs then base else
    let ground := defaultWeight base rs
    if decreasing ground rs then ground else relax base rs

theorem preserves_decreasing (base : Head s → Nat) (rs : Problem s)
    (prior : decreasing base rs ∨ decreasing (defaultWeight base rs) rs) :
    decreasing (proposeWeight base rs) rs := by
  by_cases baseOK : decreasing base rs
  · simp [proposeWeight,baseOK]
  · have groundOK := prior.resolve_left baseOK
    simp [proposeWeight,baseOK,groundOK]

end

private def Children (P : Term s → Prop) : Term s → Prop
  | .var _ | .atom _ => True
  | .free _ xs => ∀ i, P (xs i)
  | .comm _ a b | .ac _ a b => P a ∧ P b

private theorem split_all (P : Term s → Prop) {t} (all : ∀ u ∈ subterms t, P u) :
    P t ∧ Children (fun c => ∀ u ∈ subterms c, P u) t := by
  cases t with
  | var | atom => exact ⟨all _ List.mem_cons_self,trivial⟩
  | free f xs => exact ⟨all _ List.mem_cons_self,fun i u hu =>
      all _ (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hu⟩))⟩
  | comm f a b | ac f a b => exact ⟨all _ List.mem_cons_self,
      (fun u hu => all _ (List.mem_cons_of_mem _ (List.mem_append_left _ hu))),
      (fun u hu => all _ (List.mem_cons_of_mem _ (List.mem_append_right _ hu)))⟩

private theorem scale_sum {n k : Nat} (a b : Fin n → Nat) (le : ∀ i, a i ≤ b i * k) :
    (List.ofFn a).sum ≤ (List.ofFn b).sum * k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons,Nat.add_mul]
    exact Nat.add_le_add (le 0) (ih _ _ (fun i => le i.succ))

private theorem rank_le {a b : Head s → Nat} (t : Term s) (k : Nat)
    (all : ∀ u ∈ subterms t, a (head u) ≤ b (head u) * k) : rank a t ≤ rank b t * k := by
  induction t with
  | var => exact Nat.zero_le _
  | atom => exact (split_all _ all).1
  | free f xs ih =>
    obtain ⟨owner,child⟩ := split_all _ all
    change (List.ofFn (fun i => rank a (xs i))).sum + a (.free f) ≤
      ((List.ofFn (fun i => rank b (xs i))).sum + b (.free f)) * k
    rw [Nat.add_mul]
    apply Nat.add_le_add _ owner
    exact scale_sum _ _ (fun i => ih i (child i))
  | comm f x y ix iy | ac f x y ix iy =>
    obtain ⟨owner,child⟩ := split_all _ all
    change rank a x + rank a y + a _ ≤ (rank b x + rank b y + b _) * k
    simp only [Nat.add_mul]
    exact Nat.add_le_add (Nat.add_le_add
      (ix child.1)
      (iy child.2)) owner

private theorem unchanged {a b : Head s → Nat} {t : Term s}
    (all : ∀ u ∈ subterms t, a (head u) = b (head u)) : rank a t = rank b t := by
  apply Nat.le_antisymm
  · simpa using rank_le (a := a) (b := b) t 1 (fun u hu => by simp [all u hu])
  · simpa using rank_le (a := b) (b := a) t 1 (fun u hu => by simp [all u hu])

/-- Projections may inspect any operators, independent of their levels. A
ground expansion may call operators at lower levels. -/
def ExtensionRow (level : Head s → Nat) (r : Equation s) : Prop :=
  Proper r ∨
    (r.rhs.Ground ∧ (∀ u ∈ subterms r.rhs, level (head u) < level (head r.lhs)) ∧ Application r.lhs)

/-- Each row either comes from a weight-decreasing base presentation at level
zero, returns a proper subterm, or calls only lower levels in a ground result.
Rows may occur in any order, including several equations for the same head. -/
def Stratified (base : Head s → Nat) (level : Head s → Nat) (rs : Problem s) : Prop :=
  ∀ r ∈ rs,
    ((∀ u ∈ subterms r.lhs ++ subterms r.rhs, level (head u) = 0) ∧
      rank base r.rhs < rank base r.lhs ∧ TableDecrease.nonduplicating r) ∨
    ExtensionRow level r

/-- The certificate may be checked before assigning the potentially much
larger weights. Variables, declared symbols and dependency levels stay local
to the supplied presentation. -/
def accepts [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (base : Head s → Nat) (level : Head s → Nat) (rs : Problem s) : Bool :=
  rs.all fun r =>
    ((subterms r.lhs ++ subterms r.rhs).all (fun u => level (head u) == 0) &&
      decide (rank base r.rhs < rank base r.lhs) && TableDecrease.nonduplicating r) ||
    (subterms r.lhs).tail.contains r.rhs ||
    (r.rhs.variables.isEmpty && (subterms r.rhs).all (fun u => level (head u) < level (head r.lhs)) &&
      match r.lhs with | .var _ | .atom _ => false | _ => true)

theorem accepts_iff [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (base : Head s → Nat) (level : Head s → Nat) (rs : Problem s) :
    accepts base level rs ↔ Stratified base level rs := by
  have ground (t : Term s) : t.variables.isEmpty ↔ t.Ground := by
    simp [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,Term.Ground,Term.mem_variables]
  unfold accepts Stratified
  rw [List.all_eq_true]
  apply forall_congr'; intro r
  apply forall_congr'; intro _
  cases hl : r.lhs <;> simp [hl,Proper,ExtensionRow,Application,ground,and_assoc,or_assoc,-List.all_append]

theorem decreasing {base : Head s → Nat} (pos : ∀ h, 0 < base h)
    {level : Head s → Nat} {rs : Problem s} (cls : Stratified base level rs) :
    SymbolWeight.decreasing (weights base rs level) rs := by
  let w := weights base rs level
  have radixPos : 0 < radix base rs := by unfold radix; omega
  have wPos (h : Head s) : 0 < w h := Nat.mul_pos (pos h) (Nat.pow_pos radixPos)
  apply List.all_eq_true.mpr
  intro r hr
  apply Bool.and_eq_true_iff.mpr
  change decide (rank w r.rhs < rank w r.lhs) = true ∧ _
  rcases cls r hr with ⟨fixed,smaller,linear⟩ | proj | ⟨ground,below,app⟩
  · have equal {t : Term s} (h : ∀ u ∈ subterms t, level (head u) = 0) : rank w t = rank base t :=
      unchanged (fun u hu => by simp [w,weights,h u hu])
    exact ⟨decide_eq_true (by rwa [equal (fun u hu => fixed _ (List.mem_append_right _ hu)),
      equal (fun u hu => fixed _ (List.mem_append_left _ hu))]),linear⟩
  · obtain ⟨lt,vars⟩ := projection w wPos proj
    exact ⟨decide_eq_true lt,List.all_eq_true.mpr (fun v _ => decide_eq_true (vars.count_le v))⟩
  · have levelPos : 0 < level (head r.lhs) :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (below r.rhs (by cases r.rhs <;> exact List.mem_cons_self))
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt levelPos)
    have cap : rank w r.rhs ≤ rank base r.rhs * radix base rs ^ n := by
      apply rank_le
      intro u hu
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right radixPos
      have := below u hu; omega
    have smaller : rank base r.rhs < radix base rs := by
      have := FiniteOccurs.le_sum _ _ (List.mem_map.mpr ⟨r,hr,rfl⟩ : rank base r.rhs ∈ rs.map (fun t => rank base t.rhs))
      dsimp only [radix]; omega
    have root : w (head r.lhs) ≤ rank w r.lhs := by
      cases hl : r.lhs with
      | var | atom => simp [hl,Application] at app
      | free f xs => change _ ≤ _ + w (.free f); exact Nat.le_add_left _ _
      | comm f x y | ac f x y => change _ ≤ _ + w _; exact Nat.le_add_left _ _
    have strict : rank w r.rhs < w (head r.lhs) := by
      have lt := Nat.lt_of_le_of_lt cap (Nat.mul_lt_mul_of_pos_right smaller (Nat.pow_pos radixPos))
      have mul := Nat.mul_le_mul_right (radix base rs ^ (n+1)) (pos (head r.lhs))
      dsimp only [w,weights]; rw [hn]
      rw [Nat.one_mul] at mul
      apply Nat.lt_of_lt_of_le _ mul
      simpa [Nat.pow_succ,Nat.mul_comm] using lt
    have empty : r.rhs.variables = [] := List.eq_nil_iff_forall_not_mem.mpr (fun v hv =>
      ground v ((Term.mem_variables ..).mp hv))
    exact ⟨decide_eq_true (Nat.lt_of_lt_of_le strict root),by simp [TableDecrease.nonduplicating,empty]⟩

end Tamarin.SubtermDecrease
