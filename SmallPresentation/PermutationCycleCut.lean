module

public import SmallPresentation.PermutationCycleIntervalSplit

/-! Exact cycle-count change for a cut of an explicitly indexed permutation cycle.
The unchanged part of the permutation is arbitrary and can contain infinitely many
symbols when only the permutation equivalence is used; counting assumes finiteness. -/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

attribute [local instance] Classical.propDecidable

variable {D E : Type*}

/-- Switch the incoming arrows at two specified points. -/
noncomputable def cutAt (σ : Equiv.Perm D) (a b : D) : Equiv.Perm D := by
  classical
  exact σ.trans (Equiv.swap a b)

@[simp] theorem cutAt_apply (σ : Equiv.Perm D) (a b d : D) :
    cutAt σ a b d = Equiv.swap a b (σ d) := rfl

/-- Applying the same cut twice restores the original permutation. -/
theorem cutAt_cutAt (σ : Equiv.Perm D) (a b : D) : cutAt (cutAt σ a b) a b = σ := by
  classical
  ext d
  simp only [cutAt_apply, Equiv.swap_apply_self]

/-- Cuts commute with any explicit relabelling of the actual permutation. -/
theorem cutAt_intertwines (σ : Equiv.Perm D) (τ : Equiv.Perm E) (e : D ≃ E)
    (he : ∀ d, e (σ d) = τ (e d)) (a b d : D) :
    e (cutAt σ a b d) = cutAt τ (e a) (e b) (e d) := by
  classical
  rw [cutAt_apply, cutAt_apply, e.injective.map_swap, he]

/-- Relabelled cuts have exactly the same actual cycle quotient. -/
noncomputable def cutAtCyclesEquiv [Finite D] [Finite E]
    (σ : Equiv.Perm D) (τ : Equiv.Perm E) (e : D ≃ E)
    (he : ∀ d, e (σ d) = τ (e d)) (a b : D) :
    Cycles (cutAt σ a b) ≃ Cycles (cutAt τ (e a) (e b)) :=
  conjugateEquiv _ _ e (cutAt_intertwines σ τ e he a b)

/-- Cutting in one invariant summand leaves the other summand literally unchanged. -/
theorem cutAt_sum (σ : Equiv.Perm D) (τ : Equiv.Perm E) (a b : D) :
    cutAt (Equiv.sumCongr σ τ) (Sum.inl a) (Sum.inl b) =
      Equiv.sumCongr (cutAt σ a b) τ := by
  classical
  apply Equiv.ext
  intro d
  rcases d with d | d <;>
    simp only [cutAt_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.swap_apply_def]
  · split_ifs <;> simp_all
  · simp

/-- A cut of the indexed cyclic summand adds one to the exact cycle count. -/
theorem card_cutAt_sum_rotation (m n : ℕ) (τ : Equiv.Perm E) [Finite E]
    [Fintype (Cycles (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ))]
    [Fintype (Cycles (cutAt (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ)
      (Sum.inl (intervalStartLeft m n)) (Sum.inl (intervalStartRight m n))))] :
    Fintype.card (Cycles (cutAt (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ)
      (Sum.inl (intervalStartLeft m n)) (Sum.inl (intervalStartRight m n)))) =
      Fintype.card (Cycles (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ)) + 1 := by
  classical
  let := Fintype.ofFinite (Cycles τ)
  let := Fintype.ofFinite (Cycles (finRotate ((m + 1) + (n + 1))))
  let := Fintype.ofFinite (Cycles (intervalSplit m n))
  have hold := Fintype.card_congr (sumCyclesEquiv (finRotate ((m + 1) + (n + 1))) τ)
  rw [Fintype.card_sum, card_finRotateCycles _ (by omega)] at hold
  have hcut : cutAt (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ)
      (Sum.inl (intervalStartLeft m n)) (Sum.inl (intervalStartRight m n)) =
      Equiv.sumCongr (intervalSplit m n) τ := by
    rw [cutAt_sum]
    congr 1
    ext d
    simp only [cutAt_apply, intervalSplit, Equiv.trans_apply, Equiv.swap_apply_def]
    split_ifs <;> rfl
  let := Fintype.ofFinite (Cycles (Equiv.sumCongr (intervalSplit m n) τ))
  have hnew := Fintype.card_congr (sumCyclesEquiv (intervalSplit m n) τ)
  rw [Fintype.card_sum, card_intervalSplitCycles] at hnew
  have he := Fintype.card_congr (Equiv.cast (congrArg Cycles hcut))
  omega

/-- A single actual vertex split adds exactly one cycle, allowing arbitrary unchanged cycles. -/
theorem card_cutAt_of_intervalCoordinates [Finite D] [Finite E]
    (σ : Equiv.Perm D) (τ : Equiv.Perm E) (m n : ℕ)
    (e : Fin ((m + 1) + (n + 1)) ⊕ E ≃ D)
    (he : ∀ d, e (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ d) = σ (e d))
    [Fintype (Cycles σ)]
    [Fintype (Cycles (cutAt σ (e (Sum.inl (intervalStartLeft m n)))
      (e (Sum.inl (intervalStartRight m n)))))] :
    Fintype.card (Cycles (cutAt σ (e (Sum.inl (intervalStartLeft m n)))
      (e (Sum.inl (intervalStartRight m n))))) = Fintype.card (Cycles σ) + 1 := by
  classical
  let σ₀ := Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ
  let := Fintype.ofFinite (Cycles σ₀)
  let := Fintype.ofFinite (Cycles (cutAt σ₀ (Sum.inl (intervalStartLeft m n))
    (Sum.inl (intervalStartRight m n))))
  have hold := Fintype.card_congr (conjugateEquiv σ₀ σ e he)
  have hcut := Fintype.card_congr (cutAtCyclesEquiv σ₀ σ e he
    (Sum.inl (intervalStartLeft m n)) (Sum.inl (intervalStartRight m n)))
  have hcount := card_cutAt_sum_rotation m n τ
  dsimp only [σ₀] at hold hcut
  omega

end SmallPresentationStatements.PermutationCycles
