module

public import SmallPresentation.PermutationCyclePartition

/-! Removing an entire invariant cycle, including the two-corner face of a bigon. -/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D : Type*}

/-- An inhabited invariant subset consisting of one cycle contributes precisely
one extra cycle to the ambient permutation. -/
noncomputable def removeSingleCycleEquiv [Finite D] (σ : Equiv.Perm D)
    (p : D → Prop) [DecidablePred p] (hp : ∀ d, p (σ d) ↔ p d)
    (x : {d : D // p d})
    (hcycle : ∀ d e : {d : D // p d}, (σ.subtypePerm hp).SameCycle d e) :
    Cycles σ ≃ Option (Cycles (complementPerm σ p hp)) := by
  let : Subsingleton (Cycles (σ.subtypePerm hp)) := ⟨fun c d ↦ by
    induction c using Quotient.inductionOn with
    | h y =>
      induction d using Quotient.inductionOn with
      | h z => exact Quotient.sound (hcycle y z)⟩
  let : Nonempty (Cycles (σ.subtypePerm hp)) := ⟨cycle _ x⟩
  let eu : Cycles (σ.subtypePerm hp) ≃ PUnit.{1} := Equiv.punitOfNonemptyOfSubsingleton
  exact (partitionCyclesEquiv σ p hp).trans
    ((Equiv.sumCongr eu (Equiv.refl _)).trans
      ((Equiv.sumComm _ _).trans (Equiv.optionEquivSumPUnit _).symm))

theorem twoCycle_invariant (σ : Equiv.Perm D) (a b : D)
    (ha : σ a = b) (hb : σ b = a) (d : D) :
    (σ d = a ∨ σ d = b) ↔ (d = a ∨ d = b) := by
  constructor
  · rintro (h | h)
    · exact Or.inr (σ.injective (h.trans hb.symm))
    · exact Or.inl (σ.injective (h.trans ha.symm))
  · rintro (rfl | rfl)
    · exact Or.inr ha
    · exact Or.inl hb

/-- Restrict a permutation off a specified two-cycle. -/
noncomputable def offTwoPerm (σ : Equiv.Perm D) (a b : D)
    (ha : σ a = b) (hb : σ b = a) : Equiv.Perm {d : D // d ≠ a ∧ d ≠ b} := by
  classical
  exact σ.subtypePerm (fun d ↦ by
    simpa only [not_or] using not_congr (twoCycle_invariant σ a b ha hb d))

@[simp] theorem offTwoPerm_val (σ : Equiv.Perm D) (a b : D)
    (ha : σ a = b) (hb : σ b = a) (d : {d : D // d ≠ a ∧ d ≠ b}) :
    (offTwoPerm σ a b ha hb d).val = σ d.val := rfl

/-- A two-cycle can be removed with an explicit bijection on the remaining cycles. -/
noncomputable def removeTwoCycleEquiv [Finite D] (σ : Equiv.Perm D) (a b : D)
    (ha : σ a = b) (hb : σ b = a) :
    Cycles σ ≃ Option (Cycles (offTwoPerm σ a b ha hb)) := by
  classical
  let p := fun d ↦ d = a ∨ d = b
  let hp := twoCycle_invariant σ a b ha hb
  have hc : ∀ d e : {d : D // p d}, (σ.subtypePerm hp).SameCycle d e := by
    intro ⟨d, hd⟩ ⟨e, he⟩
    rw [Equiv.Perm.sameCycle_subtypePerm]
    change σ.SameCycle d e
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl
    · exact .refl _ _
    · rw [← ha]; exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    · rw [← hb]; exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    · exact .refl _ _
  let e : {d : D // ¬p d} ≃ {d : D // d ≠ a ∧ d ≠ b} :=
    Equiv.subtypeEquivRight (fun _ ↦ not_or)
  let ec := conjugateEquiv (complementPerm σ p hp) (offTwoPerm σ a b ha hb) e
    (fun _ ↦ rfl)
  exact (removeSingleCycleEquiv σ p hp ⟨a, Or.inl rfl⟩ hc).trans ec.optionCongr

/-- Removing the two-corner cycle subtracts one from the actual cycle count. -/
theorem card_offTwoPerm [Finite D] (σ : Equiv.Perm D) (a b : D)
    (ha : σ a = b) (hb : σ b = a)
    [Fintype (Cycles σ)] [Fintype (Cycles (offTwoPerm σ a b ha hb))] :
    Fintype.card (Cycles σ) = Fintype.card (Cycles (offTwoPerm σ a b ha hb)) + 1 := by
  simpa using Fintype.card_congr (removeTwoCycleEquiv σ a b ha hb)

end SmallPresentationStatements.PermutationCycles
