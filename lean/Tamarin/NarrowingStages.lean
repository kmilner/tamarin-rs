import Tamarin.VariantLayers
import Tamarin.CheckedReduction
/-! A total attempt at folding a finite prefix. A failed expansion or an open
frontier at the depth limit never produces rows. -/
namespace Tamarin.VariantLayers
variable {α : Type}

def attempt (next : α → Option (List α)) (covers : α → α → Bool) : Nat → Layers α → Option (List α)
  | 0,_ => none
  | k+1,l => do
    let groups ← l.frontier.mapM next
    let children := groups.flatten
    if children.all (fun c => l.rows.any (covers · c)) then return l.rows
    else attempt next covers k ⟨l.rows,children⟩

theorem mapM_sound {α β : Type} {f : α → Option β} {g : α → β}
    (ok : ∀ a b, f a = some b → b = g a) (xs : List α) (ys : List β) (h : xs.mapM f = some ys) :
    ys = xs.map g := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons x xs ih =>
    cases fx : f x <;> simp [List.mapM_cons,fx] at h
    next b =>
      cases tail : xs.mapM f <;> simp [tail] at h
      next bs => simp [← h,ih bs tail,ok x b fx]

theorem mapM_exact {α β : Type} {f : α → Option β} {g : α → β} (xs : List α)
    (ok : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons,ok x List.mem_cons_self,ih (fun a ha => ok a (.tail _ ha))]

private theorem closed_flat (covers : α → α → Bool) (next : α → List α) (l : Layers α) :
    (l.frontier.map next).flatten.all (fun c => l.rows.any (covers · c)) = closed covers next l := by
  apply Bool.eq_iff_iff.mpr
  simp [closed,List.all_eq_true]

theorem attempt_closed {seed : α} {next : α → List α} {test : α → Option (List α)}
    {covers : α → α → Bool} (refl : ∀ p, covers p p = true)
    (exactStep : ∀ p cs, test p = some cs → cs = next p)
    (fuel j : Nat) {rows} (hit : attempt test covers fuel (after seed next j) = some rows) :
    ClosedRows seed next covers rows := by
  induction fuel generalizing j with
  | zero => contradiction
  | succ k ih =>
    let l := after seed next j
    cases groups : l.frontier.mapM test with
    | none => dsimp only [l] at groups; simp [attempt,groups] at hit
    | some cs =>
      have same := mapM_sound exactStep l.frontier cs groups
      subst cs
      change attempt test covers (k+1) l = some rows at hit
      simp only [attempt,groups,Bind.bind,Option.bind,closed_flat] at hit
      split at hit
      · next ok => cases hit; exact stopped refl j rfl ok
      · exact ih (j+1) hit

theorem attempt_eventually {seed : α} {next : α → List α} {test : Nat → α → Option (List α)}
    {covers : α → α → Bool} (per : ∀ p, ∃ k, ∀ n ≥ k, test n p = some (next p))
    (basis : FiniteBasis seed next covers) :
    ∃ rows k, ∀ n ≥ k, attempt (test n) covers n (start seed) = some rows := by
  obtain ⟨stop,closes⟩ := eventually_closed basis
  have go (i left : Nat) (sum : i+left = stop) :
      ∃ rows k, ∀ n ≥ k, ∀ d > left, attempt (test n) covers d (after seed next i) = some rows := by
    induction left generalizing i with
    | zero =>
      obtain ⟨k,h⟩ := CheckedReduction.common_budget (after seed next i).frontier _ (fun p _ => per p)
      refine ⟨(after seed next i).rows,k,fun n hn d hd => ?_⟩
      cases d with
      | zero => omega
      | succ d =>
        have endHere : closed covers next (after seed next i) := by simpa [←sum] using closes
        simp only [attempt,mapM_exact _ (h n hn),Bind.bind,Option.bind,closed_flat,endHere,ite_true,pure]
    | succ left ih =>
      obtain ⟨k,h⟩ := CheckedReduction.common_budget (after seed next i).frontier _ (fun p _ => per p)
      by_cases stopNow : closed covers next (after seed next i)
      · refine ⟨(after seed next i).rows,k,fun n hn d hd => ?_⟩
        cases d with
        | zero => omega
        | succ d => simp only [attempt,mapM_exact _ (h n hn),Bind.bind,Option.bind,closed_flat,stopNow,ite_true,pure]
      · obtain ⟨rows,m,tail⟩ := ih (i+1) (by omega)
        refine ⟨rows,max k m,fun n hn d hd => ?_⟩
        cases d with
        | zero => omega
        | succ d =>
          simp only [attempt,mapM_exact _ (h n (Nat.le_trans (Nat.le_max_left ..) hn)),Bind.bind,Option.bind,closed_flat,stopNow]
          exact tail n (Nat.le_trans (Nat.le_max_right ..) hn) d (by omega)
  obtain ⟨rows,k,h⟩ := go 0 stop (by omega)
  exact ⟨rows,max k (stop+1),fun n hn => h n (Nat.le_trans (Nat.le_max_left ..) hn) n (by omega)⟩

end Tamarin.VariantLayers
