import Tamarin.RigidAllocation

namespace Tamarin.RigidAllocation
variable {sig : Signature}

/-- Numerical slots have a distinct scope for each returned arm. The Rust
decoder need only interpret the positive identifiers present in its rows. -/
def Live (arm : Arm) (k : UInt64) : Prop := k ≠ 0 ∧ ∃ row ∈ arm.toList, k ∈ row.toList

structure DecoderFor (f : sig.ACSym) (observed : Variable → Prop) (avoid : List Variable) where
  slot : Arm → UInt64 → Variable
  typed : ∀ a k, Live a k → (slot a k).sort = sig.acSort f
  fresh : ∀ a k, Live a k → ¬ observed (slot a k) ∧ slot a k ∉ avoid
  distinct : ∀ a i j, Live a i → Live a j → i ≠ j → slot a i ≠ slot a j

abbrev Decoder (q : Query sig) := DecoderFor q.f q.problem.Occurs

namespace Decoder
variable {q : Query sig} {avoid : List Variable} (d : Decoder q avoid)

private def short (a : Arm) (v : UInt64) (hv : Live a v) : q.Slots false :=
  ⟨d.slot a v, d.slot a v, d.typed _ _ hv, d.typed _ _ hv, by simp, (d.fresh _ _ hv).1, (d.fresh _ _ hv).1⟩

private def long (a : Arm) (u v : UInt64) (hu : Live a u) (hv : Live a v) (ne : u ≠ v) : q.Slots true :=
  ⟨d.slot a u, d.slot a v, d.typed _ _ hu, d.typed _ _ hv,
    fun _ => d.distinct a u v hu hv ne, (d.fresh _ _ hu).1, (d.fresh _ _ hv).1⟩

end Decoder

private theorem closed_ranges (q : Query sig) (avoid : List Variable) (flip shared)
    (w : q.Slots shared) (ground : ∀ v, ¬ q.a.Occurs v) (fu : w.u ∉ avoid) (fv : w.v ∉ avoid) :
    ClosedRanges q avoid (q.answer flip shared w) := by
  intro v hv t ht
  have hb : v = q.owner flip ∨ v = q.other flip ∨ v = q.z := by
    cases flip <;> simpa [Query.owner, Query.other, or_left_comm, or_assoc, or_comm] using hv
  rcases q.bound_range flip shared w hb ht with rfl | rfl | ha
  · exact ⟨w.outsideU, fu⟩
  · exact ⟨w.outsideV, fv⟩
  · exact False.elim (ground t ha)

theorem packet_correctIn {run : Bool → Array Arm} (numeric : PacketCorrect run)
    (q : Query sig) (ground : ∀ v, ¬ q.a.Occurs v)
    (reversed : Bool) (avoid : List Variable) (d : Decoder q avoid) :
    ∃ answers : List (Substitution sig),
      ((run reversed).toList.map (fun arm => decodeArm q (d.slot arm) arm)).Perm
        (answers.map fun σ => some (FreshAnswer.encode [q.x,q.y,q.z] σ).bindings) ∧
      (Outcome.complete answers).CorrectIn (q.problemOriented reversed) avoid ∧
      ∀ σ ∈ answers, ClosedRanges q avoid σ := by
  obtain ⟨s,t,u,v,w,k,hs,ht,hu,hv,huv,hw,hk,hwk,hp⟩ := numeric reversed
  have ls : Live (shortX s) s := by simp [Live, shortX, hs]
  have lt : Live (shortY t) t := by simp [Live, shortY, ht]
  have lu : Live (longX u v) u := by simp [Live, longX, hu]
  have lv : Live (longX u v) v := by simp [Live, longX, hv]
  have lw : Live (longY w k) w := by simp [Live, longY, hw]
  have lk : Live (longY w k) k := by simp [Live, longY, hk]
  let slots : (flip shared : Bool) → q.Slots shared
    | false,false => d.short _ _ ls
    | true,false => d.short _ _ lt
    | false,true => d.long _ _ _ lu lv huv
    | true,true => d.long _ _ _ lw lk hwk
  have fresh (f b : Bool) : (slots f b).u ∉ avoid ∧ (slots f b).v ∉ avoid := by
    cases f <;> cases b
    · exact ⟨(d.fresh _ _ ls).2, (d.fresh _ _ ls).2⟩
    · exact ⟨(d.fresh _ _ lu).2, (d.fresh _ _ lv).2⟩
    · exact ⟨(d.fresh _ _ lt).2, (d.fresh _ _ lt).2⟩
    · exact ⟨(d.fresh _ _ lw).2, (d.fresh _ _ lk).2⟩
  refine ⟨q.answers slots, ?_, q.correctIn slots reversed avoid fresh,
    q.forall_answers slots _ fun f b => closed_ranges q avoid f b _ ground (fresh f b).1 (fresh f b).2⟩
  have mapped := hp.map fun arm => decodeArm q (d.slot arm) arm
  simpa [Query.answers, slots, Decoder.short, Decoder.long, shortX, shortY, longX, longY,
    decodeArm, decodeRow, decodeWord, FreshAnswer.encode, Query.answer, Query.owner, Query.other,
    Query.ownerImage, Query.zImage, hs, ht, hu, hv, hw, hk,
    q.xy, q.xy.symm, q.xz.symm, q.yz.symm] using mapped

end Tamarin.RigidAllocation
