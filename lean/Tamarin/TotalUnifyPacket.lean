import Tamarin.TotalUnifyWire

/-! Independent stack interpretation of a returned binding. The statement
for a complete packet existentially quantifies its family, allowing a future
export to change the search, witness names, redundancy and answer order. -/
namespace Tamarin.TotalUnifyWire.Packet
variable {d : Dictionary}

def tokenize : List UInt64 → Option (List Token)
  | [] => some []
  | k :: id :: a :: rest => do return ⟨k,id,a⟩ :: (← tokenize rest)
  | _ => none

theorem tokenize_words (ts : List Token) : tokenize (ts.flatMap Token.words) = some ts := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp [Token.words,tokenize,ih]

def step (d : Dictionary) (stack : List (Term d.sig)) (t : Token) :
    Option (List (Term d.sig)) := do
  if t.kind ≤ 1 then return (← leaf d t.kind t.id t.arg) :: stack
  let n := t.arg.toNat
  guard (n ≤ stack.length)
  return (← app d t.kind t.id ((stack.take n).reverse)) :: stack.drop n

def execute (d : Dictionary) (code : List Token) (stack : List (Term d.sig)) :=
  code.foldlM (step d) stack

private theorem execute_append (xs ys : List Token) (stack : List (Term d.sig)) :
    execute d (xs ++ ys) stack = (execute d xs stack).bind (execute d ys) := List.foldlM_append

private theorem execute_single (t : Token) (st : List (Term d.sig)) :
    execute d [t] st = step d st t := by simp [execute]

private theorem step_app (kind id count : UInt64) (args stack : List (Term d.sig)) (t : Term d.sig)
    (hk : ¬kind ≤ 1) (n : count.toNat = args.length) (ok : app d kind id args = some t) :
    step d (args.reverse ++ stack) ⟨kind,id,count⟩ = some (t :: stack) := by
  simp [step,hk,n,ok,guard]

private theorem children {ι : Type} (args : ι → Term d.sig)
    (safe : ∀ i code, write (args i) = some code → ∀ stack,
      execute d code stack = some (args i :: stack))
    (is : List ι) (cs : List (List Token)) (h : is.mapM (fun i => write (args i)) = some cs)
    (stack : List (Term d.sig)) :
    execute d cs.flatten stack = some ((is.map args).reverse ++ stack) := by
  induction is generalizing cs stack with
  | nil => cases h; rfl
  | cons i is ih =>
    cases hx : write (args i) with
    | none => simp [hx] at h
    | some head =>
      cases ht : is.mapM (fun i => write (args i)) with
      | none => simp [hx,ht] at h
      | some tail =>
        simp [hx,ht] at h
        subst cs
        simp [execute_append,safe i head hx,ih tail ht,List.append_assoc]

theorem write_executes (t : Term d.sig) (code : List Token) (h : write t = some code)
    (stack : List (Term d.sig)) : execute d code stack = some (t :: stack) := by
  induction t generalizing code stack with
  | var v =>
    cases hp : WordEncoding.pack v.id with
    | none => simp [write,hp] at h
    | some id =>
      simp [write,hp] at h; subst code
      simp [execute,step,leaf_var,(WordEncoding.pack_iff ..).mp hp]
  | atom a =>
    cases h
    simp [execute,step,leaf_atom]
  | free f args ih =>
    cases m : (List.finRange _).mapM (fun i => write (args i)) with
    | none => simp [write,m] at h
    | some cs =>
      cases n : WordEncoding.pack (d.sig.arity f) with
      | none => simp [write,m,n] at h
      | some count =>
        simp [write,m,n] at h; subst code
        rw [execute_append,children args ih _ _ m,Option.bind_some]
        rw [execute_single]
        simp only [List.finRange,List.map_ofFn,Function.comp_def]
        exact step_app _ _ _ _ _ _ (by decide) (by simpa using (WordEncoding.pack_iff ..).mp n)
          (app_free f args)
  | comm f l r il ir | ac f l r il ir =>
    cases hl : write l with
    | none => simp [write,hl] at h
    | some left =>
      cases hr : write r with
      | none => simp [write,hl,hr] at h
      | some right =>
        simp [write,hl,hr] at h; subst code
        simp only [execute_append,il _ hl,ir _ hr,Option.bind_some]
        rw [execute_single]
        first
        | exact step_app 3 _ 2 [l,r] stack _ (by decide) rfl (app_comm f l r)
        | exact step_app 4 _ 2 [l,r] stack _ (by decide) rfl (app_ac f l r)

def readBinding (d : Dictionary) (row : Array UInt64) : Option (Variable × Term d.sig) := do
  let v :: s :: words := row.toList | none
  guard (s ≤ 4)
  let [t] ← execute d (← tokenize words) [] | none
  return (⟨v.toNat,sortOf s⟩,t)

theorem binding_read (σ : Substitution d.sig) (v : Variable) (row)
    (h : binding σ v = some row) : readBinding d row = some (v,σ.image v) := by
  cases id : WordEncoding.pack v.id with
  | none => simp [binding,id] at h
  | some key =>
    cases code : write (σ.image v) with
    | none => simp [binding,code,id] at h
    | some ts =>
      simp [binding,code,id] at h; subst row
      have fits : sortCode v.sort ≤ 4 := by cases v.sort <;> decide
      simp [readBinding,tokenize_words,write_executes _ _ code,fits,guard,sortOf_code,
        (WordEncoding.pack_iff ..).mp id]

def FieldsFit (t : Term d.sig) : Prop :=
  match t with
  | .var v => v.id < UInt64.size
  | .atom _ => True
  | .free f args => d.sig.arity f < UInt64.size ∧ ∀ i, FieldsFit (args i)
  | .comm _ l r | .ac _ l r => FieldsFit l ∧ FieldsFit r

private theorem map_exists {α β : Type} (f : α → Option β) (xs : List α)
    (ok : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨y,h⟩ := ok x List.mem_cons_self
    obtain ⟨ys,hy⟩ := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
    exact ⟨y::ys,by simp [h,hy]⟩

theorem fits_write (t : Term d.sig) (ok : FieldsFit t) : ∃ ts, write t = some ts := by
  induction t with
  | var v => simp [write,WordEncoding.pack,show v.id < UInt64.size from ok]
  | atom a => exact ⟨_,rfl⟩
  | free f args ih =>
    obtain ⟨ts,h⟩ := map_exists _ (List.finRange _) (fun i _ => ih i (ok.2 i))
    simp [write,h,WordEncoding.pack,ok.1]
  | ac f a b ia ib | comm f a b ia ib =>
    obtain ⟨xa,ha⟩ := ia ok.1
    obtain ⟨xb,hb⟩ := ib ok.2
    simp [write,ha,hb]

/-- Parse one arm separator, then precisely one row for each observed
variable. Row order follows the query's distinct variables. -/
inductive Payload (d : Dictionary) (vs : List Variable) :
    List (Array UInt64) → List (Substitution d.sig) → Prop where
  | nil : Payload d vs [] []
  | cons {bindings rest σ answers} :
      bindings.mapM (readBinding d) = some (vs.map fun v => (v,σ.image v)) →
      Payload d vs rest answers → Payload d vs (#[] :: bindings ++ rest) (σ :: answers)

def Decodes (p : Problem d.sig) (wire : Array (Array UInt64)) (answers : List (Substitution d.sig)) :=
  ∃ rows, wire.toList = #[1] :: rows ∧ Payload d p.variables.eraseDups rows answers

private theorem map_read {α β γ : Type} (f : α → Option β) (g : β → Option γ)
    (value : α → γ) (agree : ∀ x y, f x = some y → g y = some (value x))
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys) : ys.mapM g = some (xs.map value) := by
  induction xs generalizing ys with
  | nil => cases h; rfl
  | cons a as ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases tail : as.mapM f with
      | none => simp [ha,tail] at h
      | some bs =>
        simp [ha,tail] at h; subst ys
        simp [agree _ _ ha,ih _ tail]

private theorem payload (vs : List Variable) (answers : List (Substitution d.sig)) (rows)
    (h : answers.mapM (arm vs) = some rows) : Payload d vs rows.flatten answers := by
  induction answers generalizing rows with
  | nil => cases h; exact .nil
  | cons σ answers ih =>
    cases head : vs.mapM (binding σ) with
    | none => simp [arm,head] at h
    | some bs =>
      have one : arm vs σ = some (#[] :: bs) := by simp [arm,head]
      cases tail : answers.mapM (arm vs) with
      | none => simp [one,tail] at h
      | some rest =>
        simp [one,tail] at h; subst rows
        exact .cons (map_read _ _ _ (binding_read σ) _ _ head) (ih _ tail)

theorem pack_decodes (p : Problem d.sig) (answers : List (Substitution d.sig)) (wire)
    (h : pack p answers = some wire) : Decodes p wire answers := by
  cases result : answers.mapM (arm p.variables.eraseDups) with
  | none => simp [pack,result] at h
  | some rs =>
    simp [pack,result] at h; subst wire
    exact ⟨rs.flatten,by simp,payload _ _ _ result⟩

def Representable (p : Problem d.sig) (answers : List (Substitution d.sig)) : Prop :=
  ∀ σ ∈ answers, ∀ v ∈ p.variables, v.id < UInt64.size ∧ FieldsFit (σ.image v)

theorem pack_exists (p : Problem d.sig) (answers : List (Substitution d.sig))
    (h : Representable p answers) : ∃ wire, pack p answers = some wire := by
  have one (σ) (hs : σ ∈ answers) : ∃ a, arm p.variables.eraseDups σ = some a := by
    have per (v) (hv : v ∈ p.variables.eraseDups) : ∃ r, binding σ v = some r := by
      obtain ⟨fits,term⟩ := h σ hs v (List.mem_eraseDups.mp hv)
      obtain ⟨ts,ht⟩ := fits_write _ term
      simp [binding,ht,WordEncoding.pack,fits]
    obtain ⟨a,ha⟩ := map_exists _ _ per
    simp [arm,ha]
  obtain ⟨rs,hs⟩ := map_exists _ _ one
  simp [pack,hs]

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array (Array UInt64)

structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns es, input ds ns es = none → kernel ds ns es = #[#[0]]
  valid : ∀ ds ns es d p, input ds ns es = some ⟨d,p⟩ →
    (∃ answers, Decodes p (kernel ds ns es) answers ∧ (Outcome.complete answers).CorrectIn p []) ∨
    (kernel ds ns es = #[#[0]] ∧ ¬ Representable p ((MixedUnification.verified (s := d.sig)).solve p trivial []))

theorem correct : Correct run where
  malformed := fun ds ns es h => by simp [run,h]
  valid := by
    intro ds ns es d p hi
    let answers := (MixedUnification.verified (s := d.sig)).solve p trivial []
    have solved : (Outcome.complete answers).CorrectIn p [] := MixedUnification.unify_correct rfl
    cases hw : pack p answers with
    | some wire =>
      have eq : run ds ns es = wire := by simp only [run,hi]; change (pack p answers).getD _ = _; rw [hw]; rfl
      exact .inl ⟨_,eq ▸ pack_decodes _ _ _ hw,solved⟩
    | none =>
      have eq : run ds ns es = #[#[0]] := by simp only [run,hi]; change (pack p answers).getD _ = _; rw [hw]; rfl
      exact .inr ⟨eq,fun fits => by obtain ⟨_,h⟩ := pack_exists _ _ fits; rw [hw] at h; contradiction⟩

end Tamarin.TotalUnifyWire.Packet
