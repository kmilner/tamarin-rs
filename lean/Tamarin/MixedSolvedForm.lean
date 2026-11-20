import Tamarin.MixedReconstruction

/-! Assemble local solved forms. Elimination can choose any definition of a slot.
For a compatible combination the other definitions of that slot agree modulo B.
A finite model rules out a variable occurring properly in its own definition. -/
namespace Tamarin.MixedUnification.SolvedForm
variable {s : Signature}
abbrev Row (s : Signature) := Variable × Term s
abbrev Env (s : Signature) := Variable → Term s
def Models (ds : List (Row s)) (W : Env s) :=
  ∀ d ∈ ds, EquivB (W d.1) (d.2.subst W)
def Agree (ds : List (Row s)) :=
  ∀ d ∈ ds, ∀ e ∈ ds, d.1 = e.1 → EquivB d.2 e.2

/-- Each step eliminates one output from all remaining right-hand sides. The
caller checks the result against the input, including incompatible guesses. -/
def assemble (ds : List (Row s)) :
    {θ : Env s // ∀ W, Models ds W → Agree ds →
        Models ds θ ∧ ∀ v, EquivB (W v) ((θ v).subst W)} := by
  match ds with
  | [] => exact ⟨Term.var,fun _ _ _ => ⟨by simp [Models],fun _ => .refl _⟩⟩
  | (x,t) :: rest =>
    let bind (v : Variable) : Term s := if v = x then t else .var v
    let other := rest.filter (fun d => d.1 != x)
    let change (d : Row s) : Row s := (d.1, d.2.subst bind)
    let tail := other.map change
    have lt : tail.length < ((x,t)::rest).length := by
      simpa [tail,other] using Nat.lt_succ_of_le (List.length_filter_le (fun d : Row s => d.1 != x) rest)
    let next := assemble tail
    let θ := fun v => (bind v).subst next.val
    refine ⟨θ,?_⟩
    intro W model unique
    have ht := model (x,t) List.mem_cons_self
    have preserves (v) : EquivB (W v) ((bind v).subst W) := by
      by_cases eq : v = x
      · subst v; simpa [bind] using ht
      · simp [bind,eq,Term.subst]; exact .refl _
    have before (a : Term s) : EquivB (a.subst W) ((a.subst bind).subst W) := by
      rw [Term.subst_comp]; exact a.subst_equiv _ _ (fun v _ => preserves v)
    have member {d : Row s} (hd : d ∈ other) := List.mem_cons_of_mem (x,t) (List.mem_filter.mp hd).1
    obtain ⟨sol,factors⟩ := next.property W (by
      rintro _ hd
      obtain ⟨d,hm,rfl⟩ := List.mem_map.mp hd
      exact (model d (member hm)).trans (before d.2)) (by
      rintro _ ha _ hb eq
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
      exact (unique d (member hd) e (member he) eq).subst bind)
    have root : EquivB (θ x) (t.subst θ) := by
      by_cases trivial : t = .var x
      · rw [trivial]; exact .refl _
      have absent : ¬ t.Occurs x := by
        intro occ
        have less := (FiniteOccurs.occurs_nodes W x t occ).2 trivial
        exact (Nat.ne_of_lt less) (FiniteOccurs.nodes_equiv ht)
      change EquivB ((bind x).subst next.val) _
      simp only [bind,↓reduceIte]
      apply t.subst_equiv
      intro v hv
      have ne : v ≠ x := fun eq => absent (eq ▸ hv)
      simp [θ,bind,ne,Term.subst]; exact .refl _
    constructor
    · intro d hd
      by_cases eq : d.1 = x
      · rw [eq]
        exact root.trans ((unique _ List.mem_cons_self d hd eq.symm).subst θ)
      · have hr := (List.mem_cons.mp hd).resolve_left (fun h => eq (congrArg Prod.fst h))
        have hm := sol _ (List.mem_map_of_mem (f := change) (List.mem_filter.mpr ⟨hr,by simpa using eq⟩))
        change EquivB (next.val d.1) ((d.2.subst bind).subst next.val) at hm
        rw [Term.subst_comp] at hm
        simpa only [θ,bind,ite_eq_right eq,Term.subst] using hm
    · intro v
      apply (preserves v).trans
      change EquivB _ (((bind v).subst next.val).subst W)
      rw [Term.subst_comp]
      exact (bind v).subst_equiv _ _ (fun i _ => factors i)
termination_by ds.length
decreasing_by all_goals first | exact lt | simpa only [List.length_cons,List.length_map] using lt

end Tamarin.MixedUnification.SolvedForm
