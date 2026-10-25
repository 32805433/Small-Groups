module

public import SmallPresentation.CyclicModuleDirectSum
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.GeomSum

/-! Difference and norm operators for a specified finite-order additive action. -/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open scoped BigOperators

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Sum of the first `n` powers of an additive endomorphism. -/
def powerNorm (t : AddMonoid.End A) (n : ℕ) : AddMonoid.End A :=
  ∑ k ∈ Finset.range n, t ^ k

@[simp]
theorem powerNorm_zero (t : AddMonoid.End A) : powerNorm t 0 = 0 := by simp [powerNorm]

theorem powerNorm_succ (t : AddMonoid.End A) (n : ℕ) :
    powerNorm t (n + 1) = powerNorm t n + t ^ n := by
  simp [powerNorm, Finset.sum_range_succ]

theorem powerNorm_apply (t : AddMonoid.End A) (n : ℕ) (a : A) :
    powerNorm t n a = ∑ k ∈ Finset.range n, (t ^ k) a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [powerNorm_succ, Finset.sum_range_succ]
    change powerNorm t n a + (t ^ n) a = _
    rw [ih]

/-- The periodic complex of a specified action whose `n`th power is the identity. -/
def ofFiniteOrder (t : AddMonoid.End A) (n : ℕ) (ht : t ^ n = 1) : Periodic A where
  difference := (t - 1 : AddMonoid.End A)
  norm := powerNorm t n
  difference_norm := by
    intro a
    change ((t - 1) * powerNorm t n) a = 0
    rw [powerNorm, mul_geom_sum, ht, sub_self]
    rfl
  norm_difference := by
    intro a
    change (powerNorm t n * (t - 1)) a = 0
    rw [powerNorm, geom_sum_mul, ht, sub_self]
    rfl

theorem commute_powers (t : AddMonoid.End A) (s : AddMonoid.End B)
    (f : A →+ B) (hf : ∀ a, f (t a) = s (f a)) (k : ℕ) (a : A) :
    f ((t ^ k) a) = (s ^ k) (f a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, hf, ih]

/-- An intertwining map respects the norm and difference of finite-order actions. -/
theorem ofFiniteOrder_compatible (t : AddMonoid.End A) (s : AddMonoid.End B)
    (n : ℕ) (ht : t ^ n = 1) (hs : s ^ n = 1)
    (f : A →+ B) (hf : ∀ a, f (t a) = s (f a)) :
    Periodic.Compatible (ofFiniteOrder t n ht) (ofFiniteOrder s n hs) f where
  difference := by intro a; change f (t a - a) = s (f a) - f a; rw [map_sub, hf]
  norm := by
    intro a
    change f (powerNorm t n a) = powerNorm s n (f a)
    simp only [powerNorm_apply, map_sum, commute_powers t s f hf]

/-- Augmentation intertwines a finite-order action with trivial integer coefficients. -/
theorem ofFiniteOrder_integer_compatible (t : AddMonoid.End A)
    (n : ℕ) (ht : t ^ n = 1) (p : A →+ ℤ) (hp : ∀ a, p (t a) = p a) :
    Periodic.Compatible (ofFiniteOrder t n ht) (Periodic.integer n) p where
  difference := by intro a; change p (t a - a) = 0; rw [map_sub, hp, sub_self]
  norm := by
    intro a
    have hh (k : ℕ) : p ((t ^ k) a) = p a := by
      simpa using commute_powers t (1 : AddMonoid.End ℤ) p hp k a
    change p (powerNorm t n a) = (n : ℤ) * p a
    simp only [powerNorm_apply, map_sum, hh]
    simp

end SmallPresentationStatements.CyclicModule
