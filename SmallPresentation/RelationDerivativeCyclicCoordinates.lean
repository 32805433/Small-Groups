module

public import SmallPresentation.RelationDerivativeCosetAction
public import SmallPresentation.CyclicModuleRotation

/-! Finite cyclic coordinates for a direct sum whose coefficient group is constant
along each orbit. The coefficient groups need not be free or finitely generated. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.CyclicCoordinates

open DirectSum
attribute [local instance] Classical.propDecidable

variable {A : Type} (B : A → Type) (M : A → Type) [∀ a, AddCommGroup (M a)] (n : ℕ)

abbrev Index := Σ a, B a × Fin (n + 1)
abbrev Orbit := Σ a, B a
abbrev Sum := ⨁ i : Index B n, M i.1
abbrev Tuples := ⨁ i : Orbit B, Fin (n + 1) → M i.1

def indexEquiv : Index B n ≃ Σ _i : Orbit B, Fin (n + 1) where
  toFun i := ⟨⟨i.1, i.2.1⟩, i.2.2⟩
  invFun i := ⟨i.1.1, i.1.2, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def finiteEquiv (a : A) : (⨁ _j : Fin (n + 1), M a) ≃+ (Fin (n + 1) → M a) :=
  { DFinsupp.equivFunOnFintype with map_add' := fun _ _ ↦ rfl }

noncomputable def coordinates : Sum B M n ≃+ Tuples B M n := by
  classical
  exact (DirectSum.equivCongrLeft (β := fun i : Index B n ↦ M i.1) (indexEquiv B n)).trans
    ((DirectSum.sigmaCurryEquiv (δ := fun (i : Orbit B) (_ : Fin (n + 1)) ↦ M i.1)).trans
      (DFinsupp.mapRange.addEquiv (fun i : Orbit B ↦ finiteEquiv M n i.1)))

@[simp] theorem coordinates_apply (z : Sum B M n) (a : A) (b : B a) (j : Fin (n + 1)) :
    coordinates B M n z ⟨a, b⟩ j = z ⟨a, b, j⟩ := rfl

/-- The cyclic coordinate action, expressed in the original coset indexing. -/
noncomputable def action : AddMonoid.End (Sum B M n) :=
  (coordinates B M n).symm.toAddMonoidHom.comp
    ((DirectSum.map (fun i : Orbit B ↦ CyclicModule.rotation (A := M i.1) n)).comp
      (coordinates B M n).toAddMonoidHom)

@[simp] theorem action_apply (z : Sum B M n) (a : A) (b : B a) (j : Fin (n + 1)) :
    action B M n z ⟨a, b, j⟩ = z ⟨a, b, finRotate (n + 1) j⟩ := rfl

@[simp] theorem action_of (a : A) (b : B a) (j : Fin (n + 1)) (z : M a) :
    action B M n (DirectSum.of _ ⟨a, b, j⟩ z) =
      DirectSum.of _ ⟨a, b, (finRotate (n + 1)).symm j⟩ z := by
  classical
  apply DirectSum.ext
  rintro ⟨a', b', j'⟩
  rw [action_apply]
  by_cases ha : a = a'
  · subst a'
    by_cases hb : b = b'
    · subst b'
      by_cases hj : j = finRotate (n + 1) j'
      · subst j
        erw [Equiv.symm_apply_apply, DirectSum.of_eq_same, DirectSum.of_eq_same]
      · have hj' : (finRotate (n + 1)).symm j ≠ j' := by
          intro h
          apply hj
          exact (Equiv.symm_apply_eq _).mp h
        rw [DirectSum.of_eq_of_ne _ _ _ (by
          intro h
          apply hj
          exact (congrArg (fun i : Index B n ↦ i.2.2) h).symm)]
        rw [DirectSum.of_eq_of_ne _ _ _ (by
          intro h
          apply hj'
          exact (congrArg (fun i : Index B n ↦ i.2.2) h).symm)]
    · simp [DirectSum.of_apply, hb]
  · simp [DirectSum.of_apply, ha]

@[simp] theorem coordinates_action (z : Sum B M n) (i : Orbit B) :
    coordinates B M n (action B M n z) i =
      CyclicModule.rotation n (coordinates B M n z i) := rfl

theorem coordinates_power (k : ℕ) (z : Sum B M n) (i : Orbit B) :
    coordinates B M n ((action B M n ^ k) z) i =
      (CyclicModule.rotation n ^ k) (coordinates B M n z i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    change CyclicModule.rotation n (coordinates B M n ((action B M n ^ k) z) i) = _
    rw [ih]
    rfl

theorem action_period : action B M n ^ (n + 1) = 1 := by
  apply AddMonoid.End.ext
  intro z
  apply (coordinates B M n).injective
  apply DirectSum.ext
  intro i
  rw [coordinates_power, CyclicModule.rotation_pow_order]
  rfl

/-- Coordinates intertwine the genuine power norm with the regular cyclic norm. -/
theorem coordinates_compatible : CyclicModule.Periodic.Compatible
    (CyclicModule.ofFiniteOrder (action B M n) (n + 1) (action_period B M n))
    (CyclicModule.Periodic.directSum (fun i : Orbit B ↦ CyclicModule.regular (A := M i.1) n))
    (coordinates B M n).toAddMonoidHom where
  difference := by
    intro z
    change coordinates B M n (action B M n z - z) = _
    rw [map_sub]
    apply DirectSum.ext
    intro i
    funext j
    rfl
  norm := by
    classical
    intro z
    change coordinates B M n (CyclicModule.powerNorm (action B M n) (n + 1) z) = _
    rw [CyclicModule.powerNorm_apply, map_sum]
    apply DirectSum.ext
    intro i
    funext j
    simp only [DirectSum.sum_apply, Finset.sum_apply]
    simp_rw [coordinates_power]
    have h := CyclicModule.rotation_powerNorm_apply n (coordinates B M n z i) j
    rw [CyclicModule.powerNorm_apply] at h
    change (∑ k ∈ Finset.range (n + 1),
      (CyclicModule.rotation n ^ k) (coordinates B M n z i) j) =
        ∑ l, coordinates B M n z i l
    simpa only [Finset.sum_apply] using h

/-- Every coset-orbit coefficient module is exact in both cyclic parities. -/
theorem action_exact :
    (CyclicModule.ofFiniteOrder (action B M n) (n + 1) (action_period B M n)).EvenExact ∧
    (CyclicModule.ofFiniteOrder (action B M n) (n + 1) (action_period B M n)).OddExact := by
  have h := (coordinates_compatible B M n).equiv_symm
  exact ⟨CyclicModule.Periodic.evenExact_of_equiv _ _ (coordinates B M n).symm h
      (CyclicModule.Periodic.regular_directSum_exact n).1,
    CyclicModule.Periodic.oddExact_of_equiv _ _ (coordinates B M n).symm h
      (CyclicModule.Periodic.regular_directSum_exact n).2⟩

end SmallPresentationStatements.RelationDerivative.CyclicCoordinates
