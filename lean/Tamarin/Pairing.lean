import Tamarin.SortCheck
import Tamarin.VariableElimination

/-! Pairing rewriting is separate from ordinary B-unification. The only root
rules are fst(pair(a,b)) -> a and snd(pair(a,b)) -> b; there is no eta rule.
The ambient signature admits arbitrary Msg-sorted free, commutative, and AC
constructors, with no unit, idempotence, or additional rewrite equations.
Symbols are parameters; constructor extensions need no name-specific proof. -/
namespace Tamarin.Pairing
inductive Symbol where
  | pair | fst | snd
  | other (id arity : Nat)
  deriving DecidableEq, Repr

abbrev signature : Signature where
  FreeSym := Symbol
  CSym := Nat
  ACSym := Nat
  Atom := Nat × SortId
  arity := fun f => match f with | .pair => 2 | .fst | .snd => 1 | .other _ arity => arity
  inputSort := fun _ _ => .msg
  outputSort := fun _ => .msg
  cSort := fun _ => .msg
  acSort := fun _ => .msg
  atomSort := Prod.snd

abbrev PTerm := Term signature
abbrev PSubst := Substitution signature

def pair (a b : PTerm) : PTerm := .free .pair (Fin.cases a (fun _ => b))
def fst (a : PTerm) : PTerm := .free .fst (fun _ => a)
def snd (a : PTerm) : PTerm := .free .snd (fun _ => a)

/-- Context-closed reflexive transitive rewriting. The congruence constructor
allows parallel child reductions, each expandable into ordinary steps. -/
inductive Reduces : PTerm → PTerm → Prop where
  | refl (t) : Reduces t t
  | trans {a b c} : Reduces a b → Reduces b c → Reduces a c
  | free (f : Symbol) (a b : Fin (signature.arity f) → PTerm)
      (h : ∀ i, Reduces (a i) (b i)) : Reduces (.free f a) (.free f b)
  | comm (f : Nat) {a b c d} : Reduces a c → Reduces b d →
      Reduces (.comm f a b) (.comm f c d)
  | ac (f : Nat) {a b c d} : Reduces a c → Reduces b d →
      Reduces (.ac f a b) (.ac f c d)
  | fst (a b) : Reduces (fst (pair a b)) a
  | snd (a b) : Reduces (snd (pair a b)) b

def project (first : Bool) (t : PTerm) : PTerm :=
  match t with
  | .free .pair args => if first then args 0 else args 1
  | t => if first then fst t else snd t

def normalize : PTerm → PTerm
  | .var v => .var v
  | .atom a => .atom a
  | .free .pair args => pair (normalize (args 0)) (normalize (args 1))
  | .free .fst args => project true (normalize (args 0))
  | .free .snd args => project false (normalize (args 0))
  | .free (.other id n) args => .free (.other id n) (fun i => normalize (args i))
  | .comm f a b => .comm f (normalize a) (normalize b)
  | .ac f a b => .ac f (normalize a) (normalize b)

/-- Syntactic absence of redexes, independent of the candidate normalizer. -/
inductive Normal : PTerm → Prop where
  | var (v) : Normal (.var v)
  | atom (a) : Normal (.atom a)
  | pair {a b} : Normal a → Normal b → Normal (pair a b)
  | other (id n : Nat) (args : Fin n → PTerm) : (∀ i, Normal (args i)) → Normal (.free (.other id n) args)
  | comm (f : Nat) {a b} : Normal a → Normal b → Normal (.comm f a b)
  | ac (f : Nat) {a b} : Normal a → Normal b → Normal (.ac f a b)
  | fst {a} : Normal a → (∀ args, a ≠ .free .pair args) → Normal (fst a)
  | snd {a} : Normal a → (∀ args, a ≠ .free .pair args) → Normal (snd a)

theorem pair_eta (args : Fin 2 → PTerm) : pair (args 0) (args 1) = .free .pair args := by
  unfold pair
  congr; funext i
  refine Fin.cases rfl (fun j => ?_) i
  have : j = 0 := Subsingleton.elim j 0
  subst j; rfl

theorem unary_eta (args : Fin 1 → PTerm) : (fun _ : Fin 1 => args 0) = args := by
  funext i
  have : i = 0 := Subsingleton.elim i 0
  subst i; rfl

@[simp] theorem normalize_pair (a b : PTerm) : normalize (pair a b) = pair (normalize a) (normalize b) := rfl
@[simp] theorem normalize_fst (a : PTerm) : normalize (fst a) = project true (normalize a) := rfl
@[simp] theorem normalize_snd (a : PTerm) : normalize (snd a) = project false (normalize a) := rfl
@[simp] theorem subst_pair (σ : Variable → PTerm) (a b : PTerm) : (pair a b).subst σ = pair (a.subst σ) (b.subst σ) := by
  unfold pair
  simp only [Term.subst]
  congr; funext i
  refine Fin.cases rfl (fun j => ?_) i
  have : j = 0 := Subsingleton.elim j 0
  subst j; rfl
@[simp] theorem subst_fst (σ : Variable → PTerm) (a : PTerm) : (fst a).subst σ = fst (a.subst σ) := rfl
@[simp] theorem subst_snd (σ : Variable → PTerm) (a : PTerm) : (snd a).subst σ = snd (a.subst σ) := rfl

theorem project_normal (first : Bool) {t : PTerm} (h : Normal t) : Normal (project first t) := by
  cases h with
  | var v => cases first <;> constructor <;> first | constructor | (intro args h; cases h)
  | atom a => cases first <;> constructor <;> first | constructor | (intro args h; cases h)
  | pair ha hb => cases first <;> assumption
  | other id n args hn => cases first <;> constructor <;> first | exact .other id n args hn | (intro args h; cases h)
  | comm f ha hb => cases first <;> constructor <;> first | exact .comm f ha hb | (intro args h; cases h)
  | ac f ha hb => cases first <;> constructor <;> first | exact .ac f ha hb | (intro args h; cases h)
  | fst h hn => cases first <;> constructor <;> first | exact .fst h hn | (intro args h; cases h)
  | snd h hn => cases first <;> constructor <;> first | exact .snd h hn | (intro args h; cases h)

theorem normalize_normal (t : PTerm) : Normal (normalize t) := by
  induction t with
  | var v => exact .var v
  | atom a => exact .atom a
  | free f args ih =>
    cases f with
    | pair => exact .pair (ih 0) (ih 1)
    | fst => exact project_normal true (ih 0)
    | snd => exact project_normal false (ih 0)
    | other id n => exact .other id n _ ih
  | comm f _ _ ha hb => exact .comm f ha hb
  | ac f _ _ ha hb => exact .ac f ha hb

theorem normal_fixed {t : PTerm} (h : Normal t) : normalize t = t := by
  induction h with
  | var v => rfl
  | atom a => rfl
  | pair ha hb ia ib => simp [ia, ib]
  | ac f ha hb ia ib => simp only [normalize, ia, ib]
  | comm f ha hb ia ib => simp only [normalize, ia, ib]
  | other id n args hn ih => simp only [normalize, ih]
  | @fst a ha hn ih =>
    rw [normalize_fst, ih]
    cases a with
    | free f args => cases f <;> first | exact False.elim (hn _ rfl) | rfl
    | _ => rfl
  | @snd a ha hn ih =>
    rw [normalize_snd, ih]
    cases a with
    | free f args => cases f <;> first | exact False.elim (hn _ rfl) | rfl
    | _ => rfl

theorem normalize_idempotent (t : PTerm) : normalize (normalize t) = normalize t :=
  normal_fixed (normalize_normal t)

theorem project_reduces (first : Bool) (t : PTerm) :
    Reduces (if first then fst t else snd t) (project first t) := by
  cases t with
  | free f args =>
    cases f with
    | pair =>
      rw [← pair_eta args]
      cases first
      · exact .snd _ _
      · exact .fst _ _
    | fst => cases first <;> exact .refl _
    | snd => cases first <;> exact .refl _
    | other id n => cases first <;> exact .refl _
  | _ => cases first <;> exact .refl _

theorem normalize_reduces (t : PTerm) : Reduces t (normalize t) := by
  induction t with
  | var v => exact .refl _
  | atom a => exact .refl _
  | free f args ih =>
    cases f with
    | pair =>
      rw [normalize, pair_eta (fun i => normalize (args i))]
      exact .free _ _ _ ih
    | fst =>
      exact .trans (.free .fst args (fun _ => normalize (args 0))
        (fun i => by have h := Subsingleton.elim i 0; subst i; exact ih 0)) (project_reduces true _)
    | snd =>
      exact .trans (.free .snd args (fun _ => normalize (args 0))
        (fun i => by have h := Subsingleton.elim i 0; subst i; exact ih 0)) (project_reduces false _)
    | other id n => exact .free (.other id n) _ _ ih
  | comm f _ _ ha hb => exact .comm f ha hb
  | ac f _ _ ha hb => exact .ac f ha hb

theorem reduces_normalize {a b : PTerm} (h : Reduces a b) : normalize a = normalize b := by
  induction h with
  | refl t => rfl
  | trans h k ih ik => exact ih.trans ik
  | free f a b h ih => cases f <;> simp only [normalize, ih]
  | ac f h k ih ik => simp only [normalize, ih, ik]
  | comm f h k ih ik => simp only [normalize, ih, ik]
  | fst a b => rfl
  | snd a b => rfl

/-- Normal forms are unique for the specified rewrite relation. -/
theorem normal_unique {t a b : PTerm} (ha : Reduces t a) (hb : Reduces t b)
    (na : Normal a) (nb : Normal b) : a = b := by
  have h := (reduces_normalize ha).symm.trans (reduces_normalize hb)
  simpa only [normal_fixed na, normal_fixed nb] using h

theorem pair_sorted {a b : PTerm} (ha : HasSort a .msg) (hb : HasSort b .msg) :
    HasSort (pair a b) .msg := by
  apply HasSort.free
  intro i
  exact Fin.cases ha (fun _ => hb) i

theorem pair_children {args : Fin 2 → PTerm} {s : SortId}
    (h : HasSort (sig := signature) (.free .pair args) s) : ∀ i, HasSort (args i) .msg := by
  have hc := Term.checkSort_complete h
  simp only [Term.checkSort, Bool.and_eq_true, List.all_eq_true] at hc
  intro i
  exact Term.checkSort_sound _ _ (hc.2 i (List.mem_finRange i))

theorem project_sorted (first : Bool) {t : PTerm} (h : HasSort t .msg) :
    HasSort (project first t) .msg := by
  cases t with
  | free f args =>
    cases f with
    | pair => cases first <;> exact pair_children h _
    | fst => cases first <;> exact .free _ _ (fun _ => h)
    | snd => cases first <;> exact .free _ _ (fun _ => h)
    | other id n => cases first <;> exact .free _ _ (fun _ => h)
  | _ => cases first <;> exact .free _ _ (fun _ => h)

theorem normalize_sorted {t : PTerm} {s : SortId} (h : HasSort t s) :
    HasSort (normalize t) s := by
  induction h with
  | var v => exact .var v
  | atom a => exact .atom a
  | free f args h ih =>
    cases f with
    | pair => exact pair_sorted (ih 0) (ih 1)
    | fst => exact project_sorted true (ih 0)
    | snd => exact project_sorted false (ih 0)
    | other id n => exact HasSort.free (sig := signature) (.other id n) _ ih
  | comm f a b ha hb ia ib => exact .comm f _ _ ia ib
  | ac f a b ha hb ia ib => exact .ac f _ _ ia ib
  | widen h hab ih => exact .widen ih hab

end Tamarin.Pairing
