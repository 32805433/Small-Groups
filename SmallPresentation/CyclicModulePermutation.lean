module

public import SmallPresentation.CyclicModuleRotation
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Data.Finsupp.ToDFinsupp

/-! Regular coordinates for free abelian permutation modules. -/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open DirectSum
open scoped BigOperators

variable {X I : Type*}

/-- The additive endomorphism induced by a permutation of the free basis. -/
def permutationAction (σ : Equiv.Perm X) : AddMonoid.End (FreeAbelianGroup X) :=
  FreeAbelianGroup.map σ

noncomputable def finiteTupleEquiv (n : ℕ) :
    (Fin (n + 1) →₀ ℤ) ≃+ (Fin (n + 1) → ℤ) :=
  { Finsupp.equivFunOnFinite with map_add' := fun _ _ ↦ rfl }

/-- Partition the basis into finite cyclic orbits and retain finite support in the orbit index. -/
noncomputable def permutationCoordinates (n : ℕ) (e : X ≃ I × Fin (n + 1)) :
    FreeAbelianGroup X ≃+ (⨁ _ : I, Fin (n + 1) → ℤ) := by
  classical
  exact (FreeAbelianGroup.equivFinsupp X).trans <|
    (Finsupp.domCongr e).trans <|
    Finsupp.curryAddEquiv.trans <|
    finsuppAddEquivDFinsupp.trans <|
    DFinsupp.mapRange.addEquiv (fun _ ↦ finiteTupleEquiv n)

theorem permutationCoordinates_apply (n : ℕ) (e : X ≃ I × Fin (n + 1))
    (a : FreeAbelianGroup X) (i : I) (j : Fin (n + 1)) :
    permutationCoordinates n e a i j = FreeAbelianGroup.toFinsupp a (e.symm (i, j)) := by
  rfl

theorem toFinsupp_map_equiv (σ : Equiv.Perm X) (a : FreeAbelianGroup X) (x : X) :
    FreeAbelianGroup.toFinsupp (FreeAbelianGroup.map σ a) x =
      FreeAbelianGroup.toFinsupp a (σ.symm x) := by
  classical
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of y =>
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.toFinsupp_of,
      Finsupp.single_apply, ← σ.eq_symm_apply]
  | neg a ih =>
    rw [map_neg, map_neg, map_neg]
    change -_ = -_
    exact congrArg Neg.neg ih
  | add a b ha hb =>
    simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) ha hb

/-- The direction convention makes the induced coordinate action the forward rotation. -/
theorem permutationCoordinates_shift (n : ℕ) (e : X ≃ I × Fin (n + 1))
    (σ : Equiv.Perm X)
    (he : ∀ i j, σ (e.symm (i, finRotate (n + 1) j)) = e.symm (i, j))
    (a : FreeAbelianGroup X) (i : I) (j : Fin (n + 1)) :
    permutationCoordinates n e (FreeAbelianGroup.map σ a) i j =
      permutationCoordinates n e a i (finRotate (n + 1) j) := by
  rw [permutationCoordinates_apply, permutationCoordinates_apply, toFinsupp_map_equiv]
  congr 1
  exact (σ.symm_apply_eq.mpr (he i j).symm)

theorem permutationCoordinates_pow (n : ℕ) (e : X ≃ I × Fin (n + 1))
    (σ : Equiv.Perm X)
    (he : ∀ i j, σ (e.symm (i, finRotate (n + 1) j)) = e.symm (i, j))
    (k : ℕ) (a : FreeAbelianGroup X) (i : I) :
    permutationCoordinates n e ((permutationAction σ ^ k) a) i =
      (rotation n ^ k) (permutationCoordinates n e a i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    rw [pow_succ', pow_succ']
    change permutationCoordinates n e
      (FreeAbelianGroup.map σ ((permutationAction σ ^ k) a)) i j =
      (rotation n ^ k) (permutationCoordinates n e a i) (finRotate (n + 1) j)
    rw [permutationCoordinates_shift n e σ he]
    exact congrFun ih (finRotate (n + 1) j)

/-- A permutation with the specified cyclic orbit coordinates has the stated period. -/
theorem permutation_pow_order (n : ℕ) (e : X ≃ I × Fin (n + 1))
    (σ : Equiv.Perm X)
    (he : ∀ i j, σ (e.symm (i, finRotate (n + 1) j)) = e.symm (i, j)) :
    permutationAction σ ^ (n + 1) = 1 := by
  apply AddMonoid.End.ext
  intro a
  apply (permutationCoordinates n e).injective
  apply DirectSum.ext
  intro i
  rw [permutationCoordinates_pow n e σ he, rotation_pow_order]
  rfl

/-- The actual sum of powers of a free permutation module becomes coordinatewise norm. -/
theorem permutation_compatible (n : ℕ) (e : X ≃ I × Fin (n + 1))
    (σ : Equiv.Perm X)
    (he : ∀ i j, σ (e.symm (i, finRotate (n + 1) j)) = e.symm (i, j)) :
    Periodic.Compatible
      (ofFiniteOrder (permutationAction σ) (n + 1) (permutation_pow_order n e σ he))
      (Periodic.directSum (fun _ : I ↦ regular (A := ℤ) n))
      (permutationCoordinates n e).toAddMonoidHom where
  difference := by
    intro a
    change permutationCoordinates n e (FreeAbelianGroup.map σ a - a) = _
    rw [map_sub]
    apply DirectSum.ext
    intro i
    funext j
    change permutationCoordinates n e (FreeAbelianGroup.map σ a) i j -
      permutationCoordinates n e a i j = _
    rw [permutationCoordinates_shift n e σ he]
    rfl
  norm := by
    classical
    intro a
    change permutationCoordinates n e (powerNorm (permutationAction σ) (n + 1) a) = _
    rw [powerNorm_apply, map_sum]
    apply DirectSum.ext
    intro i
    funext j
    simp only [DirectSum.sum_apply, Finset.sum_apply]
    simp_rw [permutationCoordinates_pow n e σ he]
    change (∑ k ∈ Finset.range (n + 1),
      (rotation n ^ k) (permutationCoordinates n e a i) j) =
        ∑ l, permutationCoordinates n e a i l
    have h := rotation_powerNorm_apply n (permutationCoordinates n e a i) j
    rw [powerNorm_apply] at h
    simpa only [Finset.sum_apply] using h

/-- Both parities are exact on the free abelian group of any union of equal cyclic orbits. -/
theorem permutation_exact (n : ℕ) (e : X ≃ I × Fin (n + 1))
    (σ : Equiv.Perm X)
    (he : ∀ i j, σ (e.symm (i, finRotate (n + 1) j)) = e.symm (i, j)) :
    (ofFiniteOrder (permutationAction σ) (n + 1)
      (permutation_pow_order n e σ he)).EvenExact ∧
    (ofFiniteOrder (permutationAction σ) (n + 1)
      (permutation_pow_order n e σ he)).OddExact := by
  have h := (permutation_compatible n e σ he).equiv_symm
  exact ⟨Periodic.evenExact_of_equiv _ _ (permutationCoordinates n e).symm h
      (Periodic.regular_directSum_exact n).1,
    Periodic.oddExact_of_equiv _ _ (permutationCoordinates n e).symm h
      (Periodic.regular_directSum_exact n).2⟩

end SmallPresentationStatements.CyclicModule
