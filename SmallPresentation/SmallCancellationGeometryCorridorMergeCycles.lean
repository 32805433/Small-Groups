module

public import SmallPresentation.SmallCancellationGeometryCorridorCycleCuts

/-! Exact cycle membership after merging two distinct permutation cycles. -/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

attribute [local instance] Classical.propDecidable

variable {D : Type*} (σ : Equiv.Perm D) (a b : D)

private noncomputable def mergedClass (d : D) : Cycles σ := by
  classical
  exact if cycle σ d = cycle σ b then cycle σ a else cycle σ d

private theorem mergedClass_a : mergedClass σ a b a = cycle σ a := by
  classical
  simp [mergedClass]

private theorem mergedClass_b : mergedClass σ a b b = cycle σ a := by
  classical
  simp [mergedClass]

private theorem mergedClass_swap (d : D) :
    mergedClass σ a b (Equiv.swap a b d) = mergedClass σ a b d := by
  classical
  by_cases ha : d = a
  · rw [ha, Equiv.swap_apply_left, mergedClass_a, mergedClass_b]
  · by_cases hb : d = b
    · rw [hb, Equiv.swap_apply_right, mergedClass_a, mergedClass_b]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem mergedClass_cut_step (d : D) :
    mergedClass σ a b (cutAt σ a b d) = mergedClass σ a b d := by
  classical
  rw [cutAt_apply, mergedClass_swap]
  simp only [mergedClass, cycle_apply]

variable [Finite D]

/-- Original cycles remain contained in the merged cycle after a cut between distinct cycles. -/
theorem sameCycle_cutAt_of_sameCycle (hn : ¬σ.SameCycle a b) {d e : D}
    (h : σ.SameCycle d e) : (cutAt σ a b).SameCycle d e := by
  classical
  let τ := cutAt σ a b
  have hab : τ.SameCycle a b := cutAt_sameCycle_of_not_sameCycle σ a b hn
  have hswap (x : D) : τ.SameCycle x (Equiv.swap a b x) := by
    by_cases ha : x = a
    · rw [ha, Equiv.swap_apply_left]
      exact hab
    · by_cases hb : x = b
      · rw [hb, Equiv.swap_apply_right]
        exact hab.symm
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  apply sameCycle_map_of_step σ τ id ?_ h
  intro x
  change τ.SameCycle x (σ x)
  have hs : τ.SameCycle x (τ x) := Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have ht := hs.trans (hswap (τ x))
  simpa only [τ, cutAt_apply, Equiv.swap_apply_self] using ht

/-- A transposition between distinct cycles merges exactly those two cycles and changes no others. -/
theorem sameCycle_cutAt_merge_iff (hn : ¬σ.SameCycle a b) (d e : D) :
    (cutAt σ a b).SameCycle d e ↔
      σ.SameCycle d e ∨
        (σ.SameCycle d a ∨ σ.SameCycle d b) ∧
          (σ.SameCycle e a ∨ σ.SameCycle e b) := by
  classical
  constructor
  · intro h
    have hh := constant_on_cycles (cutAt σ a b) (mergedClass σ a b)
      (mergedClass_cut_step σ a b) h
    by_cases hd : cycle σ d = cycle σ b
    · by_cases he : cycle σ e = cycle σ b
      · exact Or.inl (Quotient.exact (hd.trans he.symm))
      · simp only [mergedClass, hd, he, ite_true, ite_false] at hh
        exact Or.inr ⟨Or.inr (Quotient.exact hd), Or.inl (Quotient.exact hh.symm)⟩
    · by_cases he : cycle σ e = cycle σ b
      · simp only [mergedClass, hd, he, ite_true, ite_false] at hh
        exact Or.inr ⟨Or.inl (Quotient.exact hh), Or.inr (Quotient.exact he)⟩
      · simp only [mergedClass, hd, he, ite_false] at hh
        exact Or.inl (Quotient.exact hh)
  · rintro (h | ⟨hd, he⟩)
    · exact sameCycle_cutAt_of_sameCycle σ a b hn h
    · have hab := cutAt_sameCycle_of_not_sameCycle σ a b hn
      rcases hd with hd | hd <;> rcases he with he | he
      · exact (sameCycle_cutAt_of_sameCycle σ a b hn hd).trans
          (sameCycle_cutAt_of_sameCycle σ a b hn he).symm
      · exact ((sameCycle_cutAt_of_sameCycle σ a b hn hd).trans hab).trans
          (sameCycle_cutAt_of_sameCycle σ a b hn he).symm
      · exact ((sameCycle_cutAt_of_sameCycle σ a b hn hd).trans hab.symm).trans
          (sameCycle_cutAt_of_sameCycle σ a b hn he).symm
      · exact (sameCycle_cutAt_of_sameCycle σ a b hn hd).trans
          (sameCycle_cutAt_of_sameCycle σ a b hn he).symm

/-- Every dart on an affected old cycle lies on one of the two affected new cycles. -/
theorem cutAt_affected_cycles (hne : a ≠ b) (d : D)
    (h : σ.SameCycle d a ∨ σ.SameCycle d b) :
    (cutAt σ a b).SameCycle d a ∨ (cutAt σ a b).SameCycle d b := by
  by_cases hab : σ.SameCycle a b
  · have hn := cutAt_not_sameCycle_of_sameCycle σ a b hne hab
    have hd : σ.SameCycle d a := h.elim id (fun hb ↦ hb.trans hab.symm)
    have hh := (sameCycle_cutAt_merge_iff (cutAt σ a b) a b hn d a).mp
      (by simpa only [cutAt_cutAt] using hd)
    exact hh.elim Or.inl (fun hh ↦ hh.1)
  · exact h.elim (fun ha ↦ Or.inl (sameCycle_cutAt_of_sameCycle σ a b hab ha))
      (fun hb ↦ Or.inr (sameCycle_cutAt_of_sameCycle σ a b hab hb))

end SmallPresentationStatements.PermutationCycles
