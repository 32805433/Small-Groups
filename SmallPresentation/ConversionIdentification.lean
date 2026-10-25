module

public import SmallPresentation.ConversionCentral

/-! # Identification of the normalized presentation with the derived subgroup

All maps below are induced by the printed words. The only external central-
extension input needed later is the standard identification of this derived
subgroup with the universal central extension of the perfect quotient.
-/
@[expose] public section

namespace SmallPresentationStatements.Conversion
open Word

variable {k μ : ℕ}

theorem normalizedPresentation_centralRow (T : FP k μ) (i : Fin (2 * (μ + 2))) :
    (normalizedPresentation T).relator ⟨i.val + 2, by omega⟩ =
      (centralPresentation T).relator i := by
  simp [normalizedPresentation, centralPresentation]

theorem exponent_centralPresentation (T : FP k μ) (a : Fin 2 → ℤ)
    (i : Fin (2 * (μ + 2))) : exponent a ((centralPresentation T).relator i) = 0 :=
  exponent_commutator _ _ _

theorem corrected_eval (T : FP k μ) (w : Word 2) :
    eval (correctedGenerators T) w =
      centralValue T w * (centralValue T centralSection₁)⁻¹ ^ exponent ![1, 0] w *
        (centralValue T centralSection₂)⁻¹ ^ exponent ![0, 1] w := by
  rw [correctedGenerators, eval_central_defects]
  · congr 2
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro x
    exact (centralSection₁_central T x).inv_left
  · intro x
    exact (centralSection₂_central T x).inv_left

theorem corrected_relators (T : FP k μ) (i : Fin (2 * μ + 6)) :
    eval (correctedGenerators T) ((normalizedPresentation T).relator i) = 1 := by
  rw [corrected_eval]
  by_cases h0 : i.val = 0
  · simp only [normalizedPresentation, ite_eq_left h0, exponent_centralSection₁]
    simp
  by_cases h1 : i.val = 1
  · simp only [normalizedPresentation, ite_eq_right h0, ite_eq_left h1,
      exponent_centralSection₂]
    simp
  · have hj : i.val - 2 < 2 * (μ + 2) := by omega
    have hi : i = (⟨(i.val - 2) + 2, by omega⟩ : Fin (2 * μ + 6)) := by
      apply Fin.ext
      change i.val = i.val - 2 + 2
      omega
    rw [hi, normalizedPresentation_centralRow T ⟨i.val - 2, hj⟩]
    have h := (centralPresentation T).eval_relator ⟨i.val - 2, hj⟩
    simp only [exponent_centralPresentation, zpow_zero, mul_one]
    exact h

/-- Send the normalized generators to their explicitly corrected lifts in `M`. -/
def normalizedToCentral (T : FP k μ) :
    (normalizedPresentation T).Group →* (centralPresentation T).Group :=
  presentationHom _ (correctedGenerators T) (corrected_relators T)

theorem central_relators_in_normalized (T : FP k μ) (i : Fin (2 * (μ + 2))) :
    eval (PresentedGroup.of (rels := (normalizedPresentation T).relSet))
      ((centralPresentation T).relator i) = 1 := by
  rw [← normalizedPresentation_centralRow T i]
  exact (normalizedPresentation T).eval_relator _

/-- The quotient map obtained by killing the two central-section words. -/
def centralToNormalized (T : FP k μ) :
    (centralPresentation T).Group →* (normalizedPresentation T).Group :=
  presentationHom _ PresentedGroup.of (central_relators_in_normalized T)

@[simp] theorem centralToNormalized_value (T : FP k μ) (w : Word 2) :
    centralToNormalized T (centralValue T w) =
      eval (PresentedGroup.of (rels := (normalizedPresentation T).relSet)) w :=
  presentationHom_eval _ _ _ _

@[simp] theorem centralToNormalized_of (T : FP k μ) (i : Fin 2) :
    centralToNormalized T (PresentedGroup.of i) = PresentedGroup.of i :=
  presentationHom_of _ _ _ _

@[simp] theorem normalized_section₁_eq_one (T : FP k μ) :
    eval (PresentedGroup.of (rels := (normalizedPresentation T).relSet)) centralSection₁ = 1 := by
  have h := (normalizedPresentation T).eval_relator ⟨0, by omega⟩
  simpa only [normalizedPresentation, Fin.val_mk, ite_true] using h

@[simp] theorem normalized_section₂_eq_one (T : FP k μ) :
    eval (PresentedGroup.of (rels := (normalizedPresentation T).relSet)) centralSection₂ = 1 := by
  have h := (normalizedPresentation T).eval_relator ⟨1, by omega⟩
  simpa only [normalizedPresentation, Fin.val_mk, Nat.one_ne_zero, ite_false, ite_true] using h

private theorem hom_corrected_pair {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b u v : G) (hu : f u = 1) (hv : f v = 1) (i : Fin 2) :
    f (![a * u⁻¹, b * v⁻¹] i) = (![f a, f b] : Fin 2 → H) i := by
  fin_cases i <;> simp [hu, hv]

private theorem pair_eta {A : Type*} (f : Fin 2 → A) : ![f 0, f 1] = f := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem centralToNormalized_corrected (T : FP k μ) (i : Fin 2) :
    centralToNormalized T (correctedGenerators T i) = PresentedGroup.of i := by
  have h := hom_corrected_pair (centralToNormalized T) (PresentedGroup.of 0)
    (PresentedGroup.of 1) (centralValue T centralSection₁) (centralValue T centralSection₂)
    (by rw [centralToNormalized_value, normalized_section₁_eq_one])
    (by rw [centralToNormalized_value, normalized_section₂_eq_one]) i
  simpa only [correctedGenerators, centralToNormalized_of, pair_eta] using h

theorem normalizedToCentral_left_inverse (T : FP k μ) :
    Function.LeftInverse (centralToNormalized T) (normalizedToCentral T) := by
  have h : (centralToNormalized T).comp (normalizedToCentral T) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    simp [normalizedToCentral]
  intro x
  exact DFunLike.congr_fun h x

/-- Each exponent coordinate descends through the commutation-row presentation. -/
def centralCharacter (T : FP k μ) (a : Fin 2 → ℤ) :
    (centralPresentation T).Group →* Multiplicative ℤ :=
  presentationHom _ (fun i ↦ Multiplicative.ofAdd (a i)) (by
    intro i
    simp [centralPresentation, eval_commutator, mul_comm])

theorem centralCharacter_value (T : FP k μ) (a : Fin 2 → ℤ) (w : Word 2) :
    centralCharacter T a (centralValue T w) = Multiplicative.ofAdd (exponent a w) := by
  rw [centralCharacter, centralValue, presentationHom_eval]
  have h : (fun i ↦ Multiplicative.ofAdd (a i)) =
      fun i ↦ (Multiplicative.ofAdd (1 : ℤ)) ^ a i := by
    funext i
    simp [← ofAdd_zsmul]
  rw [h, eval_zpowers]
  simp [← ofAdd_zsmul]

theorem exponent_zero_of_mem_commutator (T : FP k μ) (a : Fin 2 → ℤ) (w : Word 2)
    (hw : centralValue T w ∈ commutator (centralPresentation T).Group) :
    exponent a w = 0 := by
  have h := Abelianization.commutator_subset_ker (centralCharacter T a) hw
  rw [MonoidHom.mem_ker, centralCharacter_value] at h
  exact Multiplicative.ofAdd.injective h

theorem normalizedToCentral_range_mem (T : FP k μ)
    (q : (normalizedPresentation T).Group) :
    normalizedToCentral T q ∈ commutator (centralPresentation T).Group := by
  apply PresentedGroup.generated_by (normalizedPresentation T).relSet
    ((commutator (centralPresentation T).Group).comap (normalizedToCentral T)) _ q
  intro i
  change normalizedToCentral T (PresentedGroup.of i) ∈
    commutator (centralPresentation T).Group
  rw [normalizedToCentral, presentationHom_of]
  exact correctedGenerators_mem_commutator T i

theorem normalizedToCentral_right_inverse_on_derived (T : FP k μ)
    (x : (centralPresentation T).Group) (hx : x ∈ commutator (centralPresentation T).Group) :
    normalizedToCentral T (centralToNormalized T x) = x := by
  obtain ⟨w, hw⟩ := (centralPresentation T).exists_word x
  change centralValue T w = x at hw
  have hxw : centralValue T w ∈ commutator (centralPresentation T).Group := hw.symm ▸ hx
  have h₀ := exponent_zero_of_mem_commutator T ![1, 0] w hxw
  have h₁ := exponent_zero_of_mem_commutator T ![0, 1] w hxw
  rw [← hw, centralToNormalized_value, normalizedToCentral, presentationHom_eval,
    corrected_eval, h₀, h₁, zpow_zero, zpow_zero, mul_one, mul_one]

/-- The printed normalized presentation is exactly the derived subgroup of the printed
central-relator presentation, via the displayed corrected generators. -/
def normalizedEquivDerived (T : FP k μ) :
    (normalizedPresentation T).Group ≃* commutator (centralPresentation T).Group :=
  { (normalizedToCentral T).codRestrict _ (normalizedToCentral_range_mem T) with
    invFun := fun x ↦ centralToNormalized T x
    left_inv := normalizedToCentral_left_inverse T
    right_inv := fun x ↦ Subtype.ext (normalizedToCentral_right_inverse_on_derived T x x.property) }

end SmallPresentationStatements.Conversion
