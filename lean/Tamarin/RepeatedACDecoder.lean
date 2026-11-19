import Tamarin.ContextualReduction
import Tamarin.RootNarrowing
import Tamarin.StableVariants

/-! A unary operation may extract one common message from a nonempty AC
product of two or more copies. Mixing arbitrary such operations in a tower
gives unique normal values over a stably normal leaf, regardless of the
other equations in the live theory. -/
namespace Tamarin.Rewriting.RepeatedACDecoder
open ConstructorVariants ContextualReduction Cancellation
variable {sig : Signature} {R : Root sig}

def copies (f : sig.ACSym) (u : Term sig) : Nat → Term sig
  | 0 => u
  | n+1 => .ac f u (copies f u n)

private theorem injective_copies {f : sig.ACSym} {a b : Term sig} (k : Nat)
    (eq : EquivB (copies f a k) (copies f b k)) : EquivB a b := by
  classical
  have count (x : Term sig) (v : Class sig) (n : Nat) :
      (flatten f (copies f x n)).count v = (n+1) * (flatten f x).count v := by
    induction n with
    | zero => simp [copies]
    | succ n ih => rw [copies,flatten_ac,List.count_append,ih,Nat.succ_mul (n+1)]; omega
  apply equiv_of_flatten_perm f
  apply List.perm_iff_count.mpr; intro v
  have h := (flatten_equiv f eq).count_eq v
  rw [count,count] at h
  exact Nat.mul_left_cancel (by omega) h

structure Decoder (R : Root sig) where
  d : sig.FreeSym
  unary : sig.arity d = 1
  f : sig.ACSym
  extra : Nat
  only : ∀ xs out, R (.free d xs) out → ∀ i, EquivB (xs i) (copies f out (extra+1))

private theorem apply_copies (ρ : Substitution sig) (f : sig.ACSym) (x : Term sig) (n : Nat) :
    ρ.apply (copies f x n) = copies f (ρ.apply x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Term.ac f (ρ.apply x) (ρ.apply (copies f x n)) = _
    rw [ih]; rfl

/-- Reify the dispatcher from a complete head bucket. Association and
permutation of the repeated factors in a declared rule are immaterial. -/
def Decoder.of_bucket (rules : List (Equation sig)) (d : sig.FreeSym) (unary : sig.arity d = 1)
    (f : sig.ACSym) (extra : Nat) (apps : ∀ r ∈ rules, Application r.lhs)
    (bucket : ∀ r ∈ rules, head r.lhs = .free d → ∃ v,
      EquivB r.lhs (.free d (fun _ => copies f (.var v) (extra+1))) ∧ r.rhs = .var v) :
    Decoder (ruleRoot rules) where
  d := d
  unary := unary
  f := f
  extra := extra
  only := by
    rintro xs out ⟨r,mem,ρ,l,rfl⟩ i
    have hd := (instance_head r (apps r mem) ρ).symm.trans (congrArg head l.symm)
    obtain ⟨v,eq,h⟩ := bucket r mem hd
    have shape := eq.subst ρ.image
    change EquivB (ρ.apply r.lhs) (.free d (fun _ => ρ.apply (copies f (.var v) (extra+1)))) at shape
    rw [←l] at shape
    simpa [h,apply_copies] using (Matching.free_equiv_iff ..).mp shape i

def Decoder.app (D : Decoder R) (x : Term sig) := Term.free D.d (fun _ => x)

private theorem Decoder.hit (D : Decoder R) {x y} (h : AtRoot R (D.app x) y) :
    ∃ out, EquivB x (copies D.f out (D.extra+1)) ∧ EquivB out y := by
  obtain ⟨p,out,pre,hit,post⟩ := h
  obtain ⟨xs,rfl,args⟩ := free_equiv_view pre
  let i : Fin (sig.arity D.d) := ⟨0,by rw [D.unary]; decide⟩
  exact ⟨out,(args i).trans (D.only xs out hit i),post⟩

private theorem Decoder.functional (D : Decoder R) {u x y}
    (l : AtRoot R (D.app u) x) (r : AtRoot R (D.app u) y) : EquivB x y := by
  obtain ⟨a,ha,ra⟩ := D.hit l
  obtain ⟨b,hb,rb⟩ := D.hit r
  exact (ra.symm.trans (injective_copies _ (ha.symm.trans hb))).trans rb

private theorem Decoder.steps (D : Decoder R) {x y} (st : StepModulo R (D.app x) y) :
    AtRoot R (D.app x) y ∨ ∃ z, StepModulo R x z ∧ EquivB (D.app z) y := by
  rcases (free_iff ..).mp st with hit|⟨i,z,hit,post⟩
  · exact .inl hit
  · refine .inr ⟨z,hit,?_⟩
    apply EquivB.trans _ post
    apply EquivB.free; intro j
    have eq : j = i := Fin.ext (by have := j.isLt; have := i.isLt; have := D.unary; omega)
    simp [eq,EquivB.refl]

private theorem Decoder.norm (D : Decoder R) {x y} (nx : Normal R x) (hit : AtRoot R (D.app x) y) : Normal R y := by
  obtain ⟨a,ha,out⟩ := D.hit hit
  exact (normal_equiv R out).mp (normal_ac_children _ ((normal_equiv R ha).mp nx)).1

private inductive Value (D : Decoder R) (x : Term sig) : Term sig → Prop where
  | fire {v} (hit : AtRoot R (D.app x) v) : Value D x v
  | stuck (normal : Normal R (D.app x)) : Value D x (D.app x)

private theorem value_exists (D : Decoder R) {x} (nx : Normal R x) : ∃ v, Value D x v ∧ Normal R v := by
  by_cases yes : ∃ v, AtRoot R (D.app x) v
  · obtain ⟨v,h⟩ := yes; exact ⟨v,.fire h,D.norm nx h⟩
  · have norm : Normal R (D.app x) := by
      intro o st
      rcases D.steps st with hit|⟨v,st,_⟩
      · exact yes ⟨_,hit⟩
      · exact nx v st
    exact ⟨_,.stuck norm,norm⟩

private inductive Trace (R : Root sig) : Term sig → Term sig → Prop where
  | done {t n} (eq : EquivB t n) (norm : Normal R n) : Trace R t n
  | pending {t x n v} (D : Decoder R) (shape : EquivB (D.app x) t) (inner : Trace R x n)
      (target : Value D n v) (normal : Normal R v) : Trace R t v

private theorem Trace.rebase {t u n} (h : Trace R t n) (eq : EquivB t u) : Trace R u n := by
  cases h with
  | done e nt => exact .done (eq.symm.trans e) nt
  | pending D e c v nt => exact .pending D (e.trans eq) c v nt

private theorem from_eq {t u v : Term sig} (eq : EquivB t u) (st : StepModulo R u v) : StepModulo R t v := by
  obtain ⟨a,b,e,hit,o⟩ := st; exact ⟨a,b,eq.trans e,hit,o⟩

private theorem root_step {t v : Term sig} (hit : AtRoot R t v) : StepModulo R t v := by
  obtain ⟨a,b,e,h,o⟩ := hit; exact ⟨a,b,e,.root h,o⟩

private theorem Trace.step {t u n} (h : Trace R t n) (st : StepModulo R t u) : Trace R u n := by
  induction h generalizing u with
  | done eq nt => exact (nt _ (from_eq eq.symm st)).elim
  | @pending t x n v D shape inner target normal ih =>
    rcases D.steps (from_eq shape st) with root|⟨z,st,out⟩
    · cases inner with
      | pending C child =>
        obtain ⟨a,e,_⟩ := D.hit root
        cases (child.trans e).head_eq
      | done eq nt =>
        have onNormal : AtRoot R (D.app n) u := by
          obtain ⟨a,b,pre,hit,post⟩ := root
          exact ⟨a,b,(EquivB.free D.d _ _ (fun _ => eq.symm)).trans pre,hit,post⟩
        cases target with
        | fire hit => exact .done (D.functional onNormal hit) normal
        | stuck norm => exact (norm _ (root_step onNormal)).elim
    · exact .pending D out (ih st) target normal

private theorem Trace.finish {t n} (h : Trace R t n) (nt : Normal R t) : EquivB t n := by
  induction h with
  | done eq => exact eq
  | @pending t x n v D shape h target nv ih =>
    have nn := (normal_equiv R shape).mpr nt
    let i : Fin (sig.arity D.d) := ⟨0,by rw [D.unary]; decide⟩
    have child := ih (normal_free_child D.d _ nn i)
    have eq := shape.symm.trans (EquivB.free D.d _ _ (fun _ => child))
    cases target with
    | stuck => exact eq
    | fire hit => exact (nt _ (from_eq eq (root_step hit))).elim

/-- An arbitrary list of live projection operations may use different AC
symbols and different multiplicities at every layer. -/
def tower (ds : List (Decoder R)) (base : Term sig) := ds.foldl (fun t D => D.app t) base

theorem unique (ds : List (Decoder R)) {base : Term sig} (bn : Normal R base) {x y}
    (l : NormalForm R (tower ds base) x) (r : NormalForm R (tower ds base) y) : EquivB x y := by
  have trace {b n} (h : Trace R b n) (nt : Normal R n) (ops : List (Decoder R)) : ∃ v, Trace R (tower ops b) v := by
    induction ops generalizing b n with
    | nil => exact ⟨_,h⟩
    | cons D ops ih =>
      obtain ⟨v,hv,nv⟩ := value_exists D nt
      exact ih (.pending D (.refl _) h hv nv) nv
  obtain ⟨v,tr⟩ := trace (.done (.refl _) bn) bn ds
  have endpoint {o} (form : NormalForm R (tower ds base) o) :=
    (RootNarrowing.reduction_invariant (fun b => Trace R b v) Trace.rebase Trace.step form.1 tr).finish form.2.1
  exact (endpoint l).trans (endpoint r).symm

/-- Instance-wise functionality of the symbolic query, under precisely the
normalized caller substitutions used for variants. -/
theorem caller_unique (ds : List (Decoder R)) {base : Term sig} (stable : StableVariants.Stable R base)
    (ρ : Substitution sig) (normalized : Normalized R ρ) {x y}
    (l : NormalForm R (ρ.apply (tower ds base)) x) (r : NormalForm R (ρ.apply (tower ds base)) y) :
    EquivB x y := by
  have commute (ops : List (Decoder R)) (t : Term sig) : ρ.apply (tower ops t) = tower ops (ρ.apply t) := by
    induction ops generalizing t with
    | nil => rfl
    | cons D ops ih => exact ih (D.app t)
  rw [commute] at l r
  exact unique ds (stable ρ normalized) l r

end Tamarin.Rewriting.RepeatedACDecoder
