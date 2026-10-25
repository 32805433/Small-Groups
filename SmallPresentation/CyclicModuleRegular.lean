module

public import SmallPresentation.CyclicModuleObstruction
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Abel

/-!
# Exactness of regular cyclic modules

The cyclic norm and difference maps on a finite tuple of elements of any
abelian group have zero positive cohomology. The proof gives explicit
preimages and does not require that the coefficient group be free.
-/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A]

/-- Cyclic difference on a tuple of length `n+1`. -/
def regularDifference (n : ℕ) : (Fin (n + 1) → A) →+ (Fin (n + 1) → A) where
  toFun f i := f (finRotate (n + 1) i) - f i
  map_zero' := by ext i; simp
  map_add' := by intros f g; ext i; simp; abel

/-- Cyclic norm on a tuple, written as the constant tuple of its coordinate sum. -/
def regularNorm (n : ℕ) : (Fin (n + 1) → A) →+ (Fin (n + 1) → A) where
  toFun f _ := ∑ i, f i
  map_zero' := by ext i; simp
  map_add' := by intros f g; ext i; simp [Finset.sum_add_distrib]

/-- The periodic complex of a regular cyclic module with arbitrary abelian coefficients. -/
def regular (n : ℕ) : Periodic (Fin (n + 1) → A) where
  difference := regularDifference n
  norm := regularNorm n
  difference_norm := by intro f; ext i; simp [regularDifference, regularNorm]
  norm_difference := by
    intro f
    ext i
    change (∑ j, (f (finRotate (n + 1) j) - f j)) = 0
    rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]

theorem regular_evenExact (n : ℕ) : (regular (A := A) n).EvenExact := by
  intro f hf
  have hstep (i : Fin (n + 1)) : f (finRotate (n + 1) i) = f i := by
    have h := congrFun hf i
    exact sub_eq_zero.mp h
  have hconstant : ∀ k (hk : k < n + 1), f ⟨k, hk⟩ = f 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hs := hstep ⟨k, by omega⟩
      rw [finRotate_of_lt hk'] at hs
      exact hs.trans (ih (by omega))
  refine ⟨fun i ↦ if i = 0 then f 0 else 0, ?_⟩
  ext i
  change (∑ j : Fin (n + 1), if j = 0 then f 0 else 0) = f i
  simpa using (hconstant i.val i.isLt).symm

/-- A norm-zero tuple has a cyclic antiderivative given by partial sums. -/
theorem regular_oddExact (n : ℕ) : (regular (A := A) n).OddExact := by
  intro f hf
  let a : ℕ → A := fun k ↦ f (Fin.ofNat (n + 1) k)
  have ha (i : Fin (n + 1)) : a i.val = f i := by
    dsimp [a]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hsum : (∑ k ∈ Finset.range (n + 1), a k) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    have h0 : (∑ i, f i) = 0 := congrFun hf 0
    simpa only [ha] using h0
  let b : Fin (n + 1) → A := fun i ↦ ∑ k ∈ Finset.range i.val, a k
  refine ⟨b, ?_⟩
  ext i
  change b (finRotate (n + 1) i) - b i = f i
  by_cases hi : i.val < n
  · have hr : (finRotate (n + 1) i).val = i.val + 1 :=
      congrArg Fin.val (finRotate_of_lt hi)
    dsimp [b]
    rw [hr, Finset.sum_range_succ, ha]
    abel
  · have hilast : i = Fin.last n := by
      apply Fin.ext
      change i.val = n
      omega
    subst i
    rw [finRotate_last]
    change (∑ k ∈ Finset.range 0, a k) - (∑ k ∈ Finset.range n, a k) =
      f (Fin.last n)
    simp only [Finset.range_zero, Finset.sum_empty, zero_sub]
    rw [Finset.sum_range_succ] at hsum
    have hlast : a n = f (Fin.last n) := ha (Fin.last n)
    rw [hlast] at hsum
    exact (eq_neg_of_add_eq_zero_right hsum).symm

/-- Both positive parities of the regular cyclic complex are exact. -/
theorem regular_exact (n : ℕ) :
    (regular (A := A) n).EvenExact ∧ (regular (A := A) n).OddExact :=
  ⟨regular_evenExact n, regular_oddExact n⟩

end SmallPresentationStatements.CyclicModule
