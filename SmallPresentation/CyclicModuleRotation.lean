module

public import SmallPresentation.CyclicModuleFiniteOrder

/-! The explicit regular cyclic complex is the power-norm complex of rotation. -/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open scoped BigOperators
open Fin.NatCast

variable {A : Type*} [AddCommGroup A]

/-- Rotate the coordinates of a finite tuple by one position. -/
def rotation (n : ℕ) : AddMonoid.End (Fin (n + 1) → A) where
  toFun f i := f (finRotate (n + 1) i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem rotation_pow_apply (n k : ℕ) (f : Fin (n + 1) → A) (i : Fin (n + 1)) :
    (rotation n ^ k) f i = f (i + (k : Fin (n + 1))) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (rotation n ^ k) f (finRotate (n + 1) i) = _
    rw [ih, finRotate_apply]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    ac_rfl

theorem rotation_pow_order (n : ℕ) : rotation (A := A) n ^ (n + 1) = 1 := by
  apply AddMonoid.End.ext
  intro f
  funext i
  rw [rotation_pow_apply]
  simp

theorem rotation_powerNorm_apply (n : ℕ) (f : Fin (n + 1) → A) (i : Fin (n + 1)) :
    powerNorm (rotation n) (n + 1) f i = ∑ j, f j := by
  have h := powerNorm_apply (rotation (A := A) n) (n + 1) f
  have hi := congrFun h i
  simp only [Finset.sum_apply, rotation_pow_apply] at hi
  rw [← Fin.sum_univ_eq_sum_range] at hi
  rw [hi]
  simpa [finCycle_apply, add_comm] using Equiv.sum_comp (finCycle i) f

/-- The coordinate norm agrees with the actual sum of powers of rotation. -/
theorem regular_compatible_powerNorm (n : ℕ) :
    Periodic.Compatible (regular (A := A) n)
      (ofFiniteOrder (rotation n) (n + 1) (rotation_pow_order n))
      (AddMonoidHom.id _) where
  difference := fun _ ↦ rfl
  norm := by
    intro f
    ext i
    exact (rotation_powerNorm_apply n f i).symm

theorem rotation_evenExact (n : ℕ) :
    (ofFiniteOrder (rotation (A := A) n) (n + 1) (rotation_pow_order n)).EvenExact :=
  Periodic.evenExact_of_equiv _ _ (AddEquiv.refl _)
    (regular_compatible_powerNorm n) (regular_evenExact n)

theorem rotation_oddExact (n : ℕ) :
    (ofFiniteOrder (rotation (A := A) n) (n + 1) (rotation_pow_order n)).OddExact :=
  Periodic.oddExact_of_equiv _ _ (AddEquiv.refl _)
    (regular_compatible_powerNorm n) (regular_oddExact n)

end SmallPresentationStatements.CyclicModule
