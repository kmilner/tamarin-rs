import Tamarin.DHProductUnique

/-! A normal opaque base and a signed count for each exponent factor are
invariant along arbitrary interleavings of DH tower and product rewrites.
Opaque subterms are interpreted only when they are irreducible in the
entire active theory. -/
namespace Tamarin.Rewriting.DHTower.Spine
open DHPeer ConstructorVariants Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
noncomputable section
open Classical

private abbrev Reading (sig : Signature) := Option (Class sig × Int)

private def leafRead (R : Root sig) (t : Term sig) : Reading sig :=
  if Normal R t then some (classOf t, 0) else none

private def extend (s : Symbols sig) (base : Reading sig) (exponent : Option Int) : Reading sig := do
  let (leaf, count) ← base
  if leaf = classOf s.neutralTerm then return (leaf, count)
  return (leaf, count + (← exponent))

private def leftIx (s : Symbols sig) {f : sig.FreeSym} (hf : f = s.pow) : Fin (sig.arity f) :=
  ⟨0, by rw [hf,s.powArity]; decide⟩
private def rightIx (s : Symbols sig) {f : sig.FreeSym} (hf : f = s.pow) : Fin (sig.arity f) :=
  ⟨1, by rw [hf,s.powArity]; decide⟩

def read (s : Symbols sig) (R : Root sig) (k : Class sig) : Term sig → Option (Class sig × Int)
  | .free f xs => if h : f = s.pow then
      extend s (read s R k (xs (leftIx s h))) (Balance.read s R k (xs (rightIx s h)))
    else leafRead R (.free f xs)
  | .var v => leafRead R (.var v)
  | .atom a => leafRead R (.atom a)
  | .comm f a b => leafRead R (.comm f a b)
  | .ac f a b => leafRead R (.ac f a b)

@[simp] private theorem read_pow (s : Symbols sig) (R : Root sig) (k : Class sig) (b e) :
    read s R k (s.power b e) = extend s (read s R k b) (Balance.read s R k e) := by
  simp [Symbols.power,read,leftIx,rightIx]

private theorem other (s : Symbols sig) (R : Root sig) (k : Class sig) (t : Term sig)
    (h : head t ≠ .free s.pow) : read s R k t = leafRead R t := by
  cases t with
  | free f xs => simp [read,show f ≠ s.pow from fun eq => h (eq ▸ rfl)]
  | _ => rfl

private theorem opaque_equiv (R : Root sig) {a b : Term sig} (h : EquivB a b) :
    leafRead R a = leafRead R b := by simp only [leafRead,normal_equiv R h,show classOf a = classOf b from Quotient.sound h]

theorem equiv (s : Symbols sig) (R : Root sig) (k : Class sig) {a b} (h : EquivB a b) :
    read s R k a = read s R k b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b h ih =>
    simp only [read]; split
    · rw [ih, Balance.equiv s R k (h _)]
    · exact opaque_equiv _ (.free _ _ _ h)
  | comm_swap f a b => exact opaque_equiv _ (.comm_swap f a b)
  | comm_congr f h l _ _ => exact opaque_equiv _ (.comm_congr f h l)
  | ac_congr f h l _ _ => exact opaque_equiv _ (.ac_congr f h l)
  | ac_swap f a b => exact opaque_equiv _ (.ac_swap f a b)
  | ac_assoc f a b c => exact opaque_equiv _ (.ac_assoc f a b c)

private def Preserved {α : Type} (a b : Option α) : Prop := ∀ v, a = some v → b = some v

private theorem extend_preserves {a b : Reading sig} {n m : Option Int}
    (h : Preserved a b) (g : Balance.Preserved n m) :
    Preserved (extend s a n) (extend s b m) := by
  cases a with
  | none => simp [Preserved,extend]
  | some v =>
    have := h v rfl
    subst b
    cases v with
    | mk x i =>
      by_cases neut : x = classOf s.neutralTerm
      · simp [Preserved,extend,neut]
      · cases n with
        | none => simp [Preserved,extend,neut]
        | some j => rw [g _ rfl]; exact fun _ h => h

private theorem extend_mul (s : Symbols sig) (b : Reading sig) (n m : Option Int) :
    extend s (extend s b n) m = extend s b (Balance.plus n m) := by
  cases b with
  | none => rfl
  | some b =>
    obtain ⟨x,i⟩ := b
    by_cases neut : x = classOf s.neutralTerm <;>
      cases n <;> cases m <;> simp [extend,neut,Balance.plus,Int.add_assoc]

private theorem neutral_head (s : Symbols sig) : head s.neutralTerm ≠ .free s.pow := by
  intro h; have eq := Head.free.inj h
  have n := s.neutralArity
  change s.neutral = s.pow at eq
  rw [eq,s.powArity] at n; contradiction

private theorem opaque_red {R : Root sig} {a b : Term sig} (p : Reduces R a b) :
    Preserved (leafRead R a) (leafRead R b) := by
  by_cases n : Normal R a
  · rw [opaque_equiv _ (normal_reduces_equiv p n)]; exact fun _ h => h
  · simp [Preserved,leafRead,n]

/-- Every defined base and count survives every genuine step at any depth. -/
theorem reduces (pow : PowerBucket T) (inv : Balance.Inventory E) (k : Class sig)
    {a b} (p : Reduces (ruleRoot T.rules) a b) :
    ∀ v, read s (ruleRoot T.rules) k a = some v → read s (ruleRoot T.rules) k b = some v := by
  let R := ruleRoot T.rules
  let rd := read s R k
  have root {u v} (r : R u v) : Preserved (rd u) (rd v) := by
    by_cases h : head u = .free s.pow
    · obtain ⟨a,e,rfl⟩ := splitPower s h
      change Preserved (read s R k (s.power a e)) (read s R k v)
      cases pow.root a e (.refl _) r with
      | one hé hv =>
        obtain rfl := nullary s.oneArity hé
        rw [equiv s R k hv,read_pow]
        change Preserved (extend s (read s R k a) (Balance.read s R k s.product.one)) _
        rw [Balance.read_one]
        cases read s R k a with
        | none => exact fun _ h => h
        | some v =>
          obtain ⟨x,i⟩ := v
          by_cases neut : x = classOf s.neutralTerm <;> simp [Preserved,extend,neut]
      | neutral hn hv =>
        obtain rfl := nullary s.neutralArity hn
        rw [equiv s R k hv,read_pow]
        change Preserved (extend s (read s R k s.neutralTerm) _) (read s R k s.neutralTerm)
        rw [other _ _ _ _ (neutral_head s)]
        by_cases n : Normal R s.neutralTerm <;> simp [Preserved,extend,leafRead,n]
      | tower hb hv =>
        rw [equiv s R k hv,read_pow,equiv s R k hb,read_pow,read_pow]
        change Preserved (extend s (extend s _ _) _) (extend s _ (Balance.read s R k (s.product.mul _ _)))
        rw [Balance.read_mul,extend_mul]; exact fun _ h => h
    · change Preserved (read s R k u) _
      rw [other _ _ _ _ h]
      have n : ¬Normal R u := fun nn => nn _ ⟨_,_,.refl _,.root r,.refl _⟩
      simp [leafRead,n,Preserved]
  have freeC (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig)
      (red : Reduces R (.free f a) (.free f b))
      (args : ∀ i, Reduces R (a i) (b i)) (ih : ∀ i, Preserved (rd (a i)) (rd (b i))) :
      Preserved (rd (.free f a)) (rd (.free f b)) := by
    simp only [rd,read]; split
    · exact extend_preserves (ih _) (inv.reduces k (args _))
    · exact opaque_red red
  have stepRed {x y} (st : Step R x y) : Reduces R x y := .step ⟨_,_,.refl _,st,.refl _⟩
  have one {x y} (st : Step R x y) : Preserved (rd x) (rd y) := by
    induction st with
    | root h => exact root h
    | free f xs i st ih =>
      apply freeC _ _ _ (stepRed (.free _ _ _ st))
      · intro j; split <;> rename_i h
        · subst j; exact stepRed st
        · exact .basis (.refl _)
      · intro j; split <;> rename_i h
        · subst j; exact ih
        · exact fun _ eq => eq
    | comm_left f c st _ => exact opaque_red (stepRed (.comm_left f c st))
    | comm_right f c st _ => exact opaque_red (stepRed (.comm_right f c st))
    | ac_left f c st _ => exact opaque_red (stepRed (.ac_left f c st))
    | ac_right f c st _ => exact opaque_red (stepRed (.ac_right f c st))
  change Preserved (rd a) (rd b)
  induction p with
  | basis e => change Preserved (read s R k _) (read s R k _); rw [equiv _ _ _ e]; exact fun _ h => h
  | step h =>
    obtain ⟨_,_,e,st,e'⟩ := h
    change Preserved (read s R k _) (read s R k _)
    rw [equiv _ _ _ e,← equiv _ _ _ e']; exact one st
  | trans _ _ ih ik => exact fun v h => ik v (ih v h)
  | free f a b p ih => exact freeC _ _ _ (.free f a b p) p ih
  | comm f h l _ _ => exact opaque_red (.comm f h l)
  | ac f h l _ _ => exact opaque_red (.ac f h l)

private theorem power_sorts {b e : Term sig} (typed : HasSort (s.power b e) .msg) :
    HasSort b .msg ∧ HasSort e .msg := by
  have hs := Term.checkSort_complete typed
  simp only [Symbols.power,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at hs
  have arg := fun i => Term.checkSort_sound _ _ (hs.2 i (List.mem_finRange i))
  exact ⟨by simpa [s.powInput,leftIx] using arg (leftIx s rfl),
    by simpa [s.powInput,rightIx] using arg (rightIx s rfl)⟩

private theorem power_typed {b e : Term sig} (hb : HasSort b .msg) (he : HasSort e .msg) :
    HasSort (s.power b e) .msg := by
  rw [← s.powSort]; apply HasSort.free; intro i; rw [s.powInput]; split <;> assumption

/-- In a normal form the base is plain, and the exponent is either
the unit (the plain base itself) or the unique explicit power argument. -/
private theorem normal_view (pow : PowerBucket T)
    (unit : Normal (ruleRoot T.rules) s.product.one) {t : Term sig}
    (typed : HasSort t .msg) (nf : Normal (ruleRoot T.rules) t) :
    ∃ b e, HasSort e .msg ∧ Normal (ruleRoot T.rules) e ∧
      ((e = s.product.one ∧ t = b) ∨ (head e ≠ .free s.one ∧ t = s.power b e)) ∧
      ∀ k j, Balance.read s (ruleRoot T.rules) k e = some j →
        read s (ruleRoot T.rules) k t = some (classOf b,j) := by
  by_cases hp : head t = .free s.pow
  · obtain ⟨b,e,rfl⟩ := splitPower s hp
    obtain ⟨hb,he⟩ := power_sorts typed
    obtain ⟨nb,ne,bp,bn,eu⟩ := (pow.normal_iff hb he).mp nf
    refine ⟨b,e,he,ne,.inr ⟨eu,rfl⟩,?_⟩
    have distinct : classOf b ≠ classOf s.neutralTerm := fun eq => bn (Quotient.exact eq : EquivB _ _).head_eq
    intro k j hj
    simp [read_pow,other s _ _ b bp,leafRead,nb,extend,distinct,hj]
  · have sorted : HasSort s.product.one .msg := by
      rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)
    refine ⟨t,s.product.one,sorted,unit,.inl ⟨rfl,rfl⟩,?_⟩
    intro k j h
    simpa [other s _ _ t hp,leafRead,nf] using h

/-- Irreducible messages with identical defined readings are identical
modulo B. Only the inventoried group and power heads constrain the theory. -/
theorem injective (pow : PowerBucket T) (unit : Normal (ruleRoot T.rules) s.product.one)
    {u v : Term sig} (su : HasSort u .msg) (sv : HasSort v .msg)
    (nu : Normal (ruleRoot T.rules) u) (nv : Normal (ruleRoot T.rules) v)
    (same : ∀ k, read s (ruleRoot T.rules) k u = read s (ruleRoot T.rules) k v)
    (E : ExtraTable T) : EquivB u v := by
  classical
  obtain ⟨b,e,he,ne,uShape,ur⟩ := normal_view pow unit su nu
  obtain ⟨c,f,hf,nf,vShape,vr⟩ := normal_view pow unit sv nv
  have components k : classOf b = classOf c ∧
      Balance.read s (ruleRoot T.rules) k e = Balance.read s (ruleRoot T.rules) k f := by
    obtain ⟨i,hi⟩ := Balance.defined s _ k ne
    obtain ⟨j,hj⟩ := Balance.defined s _ k nf
    have eq := same k
    rw [ur k i hi, vr k j hj,Option.some.injEq,Prod.mk.injEq] at eq
    exact ⟨eq.1,hi.trans ((congrArg some eq.2).trans hj.symm)⟩
  have base : EquivB b c := Quotient.exact (components (classOf b)).1
  obtain ⟨_,_,ce⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) he ne
  obtain ⟨_,_,cf⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) hf nf
  have exp := ce.injective cf (fun k => (components k).2)
  rcases uShape with ⟨rfl,rfl⟩ | ⟨enu,rfl⟩ <;> rcases vShape with ⟨rfl,rfl⟩ | ⟨fnu,rfl⟩
  · exact base
  · exact False.elim (fnu exp.head_eq.symm)
  · exact False.elim (enu exp.head_eq)
  · apply EquivB.free; intro i; split <;> assumption

def Defined (s : Symbols sig) (R : Root sig) (t : Term sig) : Prop :=
  ∀ k, ∃ n, read s R k t = some n

theorem defined_power {R : Root sig} {b e : Term sig} (base : Defined s R b)
    (exponent : ∀ k, ∃ j, Balance.read s R k e = some j) : Defined s R (s.power b e) := by
  intro k
  obtain ⟨⟨c,n⟩,bn⟩ := base k
  obtain ⟨j,ej⟩ := exponent k
  by_cases hn : c = classOf s.neutralTerm <;> simp [read_pow,bn,ej,extend,hn]

theorem defined_normal (s : Symbols sig) (R : Root sig) {t : Term sig}
    (nf : Normal R t) : Defined s R t := by
  induction t with
  | free f xs ih =>
    by_cases h : f = s.pow
    · subst f
      intro k
      obtain ⟨⟨c,n⟩,bn⟩ := ih (leftIx s rfl) (normal_free_child _ _ nf _) k
      obtain ⟨j,ej⟩ := Balance.defined s R k (normal_free_child _ _ nf (rightIx s rfl))
      by_cases h : c = classOf s.neutralTerm <;> simp [read,bn,ej,extend,h]
    · intro k; simp [read,h,leafRead,nf]
  | var | atom | comm | ac => intro k; simp [read,leafRead,nf]

/-- Uniqueness for arbitrary nested, interleaved powers of atoms, products, or
inverse expressions with defined readings. A separate forward reduction can
exhibit a particular normal representative. -/
theorem unique (pow : PowerBucket T) (inv : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {t u v : Term sig}
    (ht : HasSort t .msg) (domain : Defined s (ruleRoot T.rules) t)
    (nu : NormalForm (ruleRoot T.rules) t u) (nv : NormalForm (ruleRoot T.rules) t v) :
    EquivB u v := by
  apply injective pow unit (nu.2.2 _ ht) (nv.2.2 _ ht) nu.2.1 nv.2.1 _ E
  intro k
  obtain ⟨n,hn⟩ := domain k
  exact (reduces pow inv k nu.1 n hn).trans (reduces pow inv k nv.1 n hn).symm

/-- The exponent list is in inner-to-outer order. The nonempty product
uses the same association as the AC argument-vector interpretation. -/
abbrev tower (s : Symbols sig) (base first : Term sig) (rest : List (Term sig)) :=
  rest.foldl s.power (s.power base first)

theorem flatten (T : Table s) {b e : Term sig} (rest : List (Term sig))
    (hb : HasSort b .msg) (he : HasSort e .msg) (hs : ∀ t ∈ rest, HasSort t .msg) :
    Reduces (ruleRoot T.rules) (tower s b e rest) (s.power b (ACRepresentation.fold s.mul e rest)) := by
  induction rest generalizing b e with
  | nil => exact .basis (.refl _)
  | cons r rs ih =>
    have hr := hs r List.mem_cons_self
    have tail := fun t h => hs t (List.mem_cons_of_mem _ h)
    have hp : HasSort (ACRepresentation.fold s.mul r rs) .msg :=
      s.mulSort ▸ ACRepresentation.fold_hasSort _ _ _ (s.mulSort ▸ hr) (fun t h => s.mulSort ▸ tail t h)
    refine (ih (power_typed hb he) hr tail).trans ?_
    let env (i : Fin 3) := if i = 0 then b else if i = 1 then e else ACRepresentation.fold s.mul r rs
    have typed : ∀ i, HasSort (env i) .msg := by
      intro i; unfold env; split <;> first | assumption | split <;> assumption
    exact T.fire .tower env typed

theorem defined_tower (s : Symbols sig) (R : Root sig) {b e : Term sig} (rest : List (Term sig))
    (nb : Normal R b) (ne : Normal R e) (ns : ∀ t ∈ rest, Normal R t) :
    Defined s R (tower s b e rest) := by
  have fold (rs : List (Term sig)) (t : Term sig) (input : Defined s R t)
      (normal : ∀ x ∈ rs, Normal R x) : Defined s R (rs.foldl s.power t) := by
    induction rs generalizing t with
    | nil => exact input
    | cons x xs ih =>
      exact ih _ (defined_power input (fun k => Balance.defined s R k (normal x List.mem_cons_self)))
        (fun y h => normal y (List.mem_cons_of_mem _ h))
  exact fold _ _ (defined_power (defined_normal s R nb) (fun k => Balance.defined s R k ne)) ns

theorem tower_typed (s : Symbols sig) {b e : Term sig} (rest : List (Term sig))
    (hb : HasSort b .msg) (he : HasSort e .msg) (hs : ∀ t ∈ rest, HasSort t .msg) :
    HasSort (tower s b e rest) .msg ∧ (tower s b e rest).rootSort = .msg := by
  induction rest generalizing b e with
  | nil => exact ⟨power_typed hb he,s.powSort⟩
  | cons r rs ih => exact ih (power_typed hb he) (hs r List.mem_cons_self) (fun t h => hs _ (List.mem_cons_of_mem _ h))

private theorem sorted_flat (s : Symbols sig) {b e : Term sig} (rest : List (Term sig))
    (hb : HasSort b .msg) (he : HasSort e .msg) (hs : ∀ t ∈ rest, HasSort t .msg) :
    HasSort (s.power b (ACRepresentation.fold s.mul e rest)) .msg :=
  power_typed hb (s.mulSort ▸ ACRepresentation.fold_hasSort _ _ _ (s.mulSort ▸ he) (fun t h => s.mulSort ▸ hs t h))

theorem from_flat {b e : Term sig} (rest : List (Term sig))
    (hb : HasSort b .msg) (he : HasSort e .msg) (hs : ∀ t ∈ rest, HasSort t .msg) {v}
    (nf : NormalForm (ruleRoot T.rules) (s.power b (ACRepresentation.fold s.mul e rest)) v) :
    NormalForm (ruleRoot T.rules) (tower s b e rest) v := by
  refine ⟨(flatten T rest hb he hs).trans nf.1,nf.2.1,?_⟩
  intro k h
  exact .widen (nf.2.2 .msg (sorted_flat s rest hb he hs)) ((tower_typed s rest hb he hs).2 ▸ Term.rootSort_le h)

/-- A computed flat normal form reconstructs every normal result of the
original tower. Different rewrite orders at intermediate powers are allowed. -/
theorem normalForm_iff_flat (pow : PowerBucket T) (inv : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {b e : Term sig} (rest : List (Term sig))
    (hb : HasSort b .msg) (he : HasSort e .msg) (hs : ∀ t ∈ rest, HasSort t .msg)
    (nb : Normal (ruleRoot T.rules) b) (ne : Normal (ruleRoot T.rules) e)
    (ns : ∀ t ∈ rest, Normal (ruleRoot T.rules) t)
    (existsFlat : ∃ v, NormalForm (ruleRoot T.rules) (s.power b (ACRepresentation.fold s.mul e rest)) v)
    (u : Term sig) : NormalForm (ruleRoot T.rules) (tower s b e rest) u ↔
      NormalForm (ruleRoot T.rules) (s.power b (ACRepresentation.fold s.mul e rest)) u := by
  refine ⟨?_,from_flat rest hb he hs⟩
  intro nf
  obtain ⟨v,hv⟩ := existsFlat
  have same := unique pow inv unit (tower_typed s rest hb he hs).1 (defined_tower s _ rest nb ne ns)
    (from_flat rest hb he hs hv) nf
  refine ⟨hv.1.trans (.basis same),nf.2.1,fun k sorted =>
    Term.checkSort_sound _ _ ((SortClash.check_equiv same k) ▸ Term.checkSort_complete (hv.2.2 k sorted))⟩

end
end Tamarin.Rewriting.DHTower.Spine
