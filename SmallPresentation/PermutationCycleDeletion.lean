module

public import SmallPresentation.PermutationCycles

/-! Removing a marked point from a permutation cycle. Deleting a non-fixed point
preserves the actual quotient of cycles, not merely its cardinality. -/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D : Type*} (σ : Equiv.Perm D) (a : D)

/-- Redirect the predecessor of `a` to its successor and fix `a` itself. -/
noncomputable def bypass : Equiv.Perm D := by
  classical
  exact σ.trans (Equiv.swap a (σ a))

@[simp] theorem bypass_self : bypass σ a a = a := by
  classical
  simp [bypass]

theorem bypass_ne_iff (d : D) : bypass σ a d ≠ a ↔ d ≠ a := by
  have h : bypass σ a d ≠ bypass σ a a ↔ d ≠ a := (bypass σ a).injective.ne_iff
  simpa only [bypass_self] using h

/-- The permutation with the marked point deleted from its cycles. -/
noncomputable def contract : Equiv.Perm {d : D // d ≠ a} :=
  (bypass σ a).subtypePerm (bypass_ne_iff σ a)

theorem contract_val_eq (d : {d : D // d ≠ a}) (h : σ d = a) :
    (contract σ a d).val = σ a := by
  classical
  change Equiv.swap a (σ a) (σ d.val) = σ a
  rw [h, Equiv.swap_apply_left]

theorem contract_val_ne (d : {d : D // d ≠ a}) (h : σ d ≠ a) :
    (contract σ a d).val = σ d := by
  classical
  change Equiv.swap a (σ a) (σ d.val) = σ d.val
  exact Equiv.swap_apply_of_ne_of_ne h (σ.injective.ne d.property)

/-- Deletion replaces a contracted step by one or two steps of the original permutation. -/
theorem contract_step (d : {d : D // d ≠ a}) :
    σ.SameCycle d.val (contract σ a d).val := by
  by_cases h : σ d.val = a
  · rw [contract_val_eq σ a d h]
    have hh : σ.SameCycle d.val (σ (σ d.val)) := Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    simpa only [h] using hh
  · rw [contract_val_ne σ a d h]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- Inclusion sends each contracted cycle to its original cycle. -/
noncomputable def includeContractCycles [Finite D] : Cycles (contract σ a) → Cycles σ :=
  Quotient.map Subtype.val (fun _ _ h ↦ sameCycle_map_of_step (contract σ a) σ Subtype.val
    (contract_step σ a) h)

variable (ha : σ a ≠ a)

/-- Replace the deleted point by its successor, leaving all surviving points unchanged. -/
noncomputable def collapsePoint (d : D) : {d : D // d ≠ a} := by
  classical
  exact if h : d = a then ⟨σ a, ha⟩ else ⟨d, h⟩

@[simp] theorem collapsePoint_self : collapsePoint σ a ha a = ⟨σ a, ha⟩ := by
  classical
  simp [collapsePoint]

@[simp] theorem collapsePoint_subtype (d : {d : D // d ≠ a}) :
    collapsePoint σ a ha d.val = d := by
  classical
  simp [collapsePoint, d.property]

theorem collapsePoint_step (d : D) :
    (contract σ a).SameCycle (collapsePoint σ a ha d) (collapsePoint σ a ha (σ d)) := by
  by_cases hd : d = a
  · subst d
    rw [collapsePoint_self, collapsePoint_subtype σ a ha ⟨σ a, ha⟩]
  · let x : {d : D // d ≠ a} := ⟨d, hd⟩
    have hc : contract σ a x = collapsePoint σ a ha (σ d) := by
      by_cases h : σ d = a
      · rw [h, collapsePoint_self]
        apply Subtype.ext
        exact contract_val_eq σ a x h
      · rw [collapsePoint_subtype σ a ha ⟨σ d, h⟩]
        apply Subtype.ext
        exact contract_val_ne σ a x h
    rw [← hc, collapsePoint_subtype σ a ha x]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- The inverse on cycle classes collapses the removed point into its original cycle. -/
noncomputable def collapseCycles [Finite D] : Cycles σ → Cycles (contract σ a) :=
  Quotient.map (collapsePoint σ a ha)
    (fun _ _ h ↦ sameCycle_map_of_step σ (contract σ a) (collapsePoint σ a ha)
      (collapsePoint_step σ a ha) h)

/-- Deleting a non-fixed point leaves the exact set of cycles unchanged. -/
noncomputable def contractCyclesEquiv [Finite D] : Cycles (contract σ a) ≃ Cycles σ where
  toFun := includeContractCycles σ a
  invFun := collapseCycles σ a ha
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      change cycle (contract σ a) (collapsePoint σ a ha d.val) = cycle (contract σ a) d
      rw [collapsePoint_subtype]
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      change cycle σ (collapsePoint σ a ha d).val = cycle σ d
      by_cases hd : d = a
      · subst d
        rw [collapsePoint_self]
        exact cycle_apply σ a
      · rw [collapsePoint_subtype σ a ha ⟨d, hd⟩]

end SmallPresentationStatements.PermutationCycles
