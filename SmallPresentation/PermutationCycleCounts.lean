module

public import SmallPresentation.PermutationCycles
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Cycle counts of identity permutations and finite cyclic rotations. -/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D : Type*}

/-- Identity permutations have one singleton cycle for each element. -/
noncomputable def identityCycles : Cycles (Equiv.refl D) ≃ D :=
  (Equiv.ofBijective (cycle (Equiv.refl D)) ⟨by
    intro x y h
    have hh := Quotient.exact h
    change (1 : Equiv.Perm D).SameCycle x y at hh
    exact Equiv.Perm.sameCycle_one.mp hh,
    fun c ↦ Quotient.inductionOn c (fun d ↦ ⟨d, rfl⟩)⟩).symm

/-- Every pair of positions belongs to the same finite rotation cycle. -/
theorem finRotate_sameCycle {n : ℕ} (x y : Fin n) : (finRotate n).SameCycle x y := by
  let : NeZero n := NeZero.of_pos x.pos
  refine ⟨((y - x).val : ℤ), ?_⟩
  rw [zpow_natCast, Equiv.Perm.coe_pow]
  rw [← finCycle_eq_finRotate_iterate]
  change x + (y - x) = y
  rw [add_comm, sub_add_cancel]

/-- A nonempty cyclic order determines exactly one vertex cycle. -/
theorem card_finRotateCycles (n : ℕ) (hn : 0 < n)
    [Fintype (Cycles (finRotate n))] : Fintype.card (Cycles (finRotate n)) = 1 := by
  let : Subsingleton (Cycles (finRotate n)) := ⟨fun c d ↦ by
    induction c using Quotient.inductionOn with
    | h x =>
      induction d using Quotient.inductionOn with
      | h y => exact Quotient.sound (finRotate_sameCycle x y)⟩
  let : Unique (Cycles (finRotate n)) :=
    { default := cycle _ ⟨0, hn⟩, uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact Fintype.card_unique

end SmallPresentationStatements.PermutationCycles
