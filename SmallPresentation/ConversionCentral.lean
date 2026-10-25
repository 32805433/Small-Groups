module

public import SmallPresentation.ConversionPerfect

/-! # The explicit central-relator presentation

This models `F/[F,R]` by the displayed commutation rows and proves that the
literal determinant-one words give central lifts of the two abelian generators.
-/
@[expose] public section

namespace SmallPresentationStatements.Conversion
open Word

/-- The presentation map associated with values of the generators satisfying every row. -/
def presentationHom {n m : ℕ} (P : FP n m) {G : Type*} [Group G]
    (f : Fin n → G) (h : ∀ i, eval f (P.relator i) = 1) : P.Group →* G := by
  apply PresentedGroup.toGroup (f := f)
  rintro _ ⟨i, rfl⟩
  exact h i

@[simp] theorem presentationHom_of {n m : ℕ} (P : FP n m) {G : Type*} [Group G]
    (f : Fin n → G) (h : ∀ i, eval f (P.relator i) = 1) (i : Fin n) :
    presentationHom P f h (PresentedGroup.of i) = f i := by
  simp only [presentationHom, PresentedGroup.toGroup.of]

@[simp] theorem presentationHom_eval {n m : ℕ} (P : FP n m) {G : Type*} [Group G]
    (f : Fin n → G) (h : ∀ i, eval f (P.relator i) = 1) (w : Word n) :
    presentationHom P f h (eval (PresentedGroup.of (rels := P.relSet)) w) = eval f w := by
  rw [map_eval]
  simp

/-- The commutation rows presenting `M = F/[F,R]`. -/
def centralPresentation {k μ : ℕ} (T : FP k μ) : FP 2 (2 * (μ + 2)) where
  relator i := commutator (gen (if i.val % 2 = 0 then 0 else 1))
    ((perfectification T).relator ⟨i.val / 2, by omega⟩)

theorem centralPresentation_row {k μ : ℕ} (T : FP k μ) (j : Fin (μ + 2)) (g : Fin 2) :
    (centralPresentation T).relator ⟨2 * j.val + g.val, by omega⟩ =
      commutator (gen g) ((perfectification T).relator j) := by
  fin_cases g
  · simp [centralPresentation]
  · have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
    simp [centralPresentation, hdiv]

def centralValue {k μ : ℕ} (T : FP k μ) (w : Word 2) : (centralPresentation T).Group :=
  eval (PresentedGroup.of (rels := (centralPresentation T).relSet)) w

theorem perfectification_row_central {k μ : ℕ} (T : FP k μ) (j : Fin (μ + 2))
    (x : (centralPresentation T).Group) :
    Commute (centralValue T ((perfectification T).relator j)) x := by
  let s := centralValue T ((perfectification T).relator j)
  have hg (g : Fin 2) : PresentedGroup.of (rels := (centralPresentation T).relSet) g ∈
      Subgroup.centralizer ({s} : Set (centralPresentation T).Group) := by
    have h := (centralPresentation T).eval_relator ⟨2 * j.val + g.val, by omega⟩
    rw [centralPresentation_row] at h
    simp only [eval_commutator, eval_gen] at h
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [s, centralValue, mul_assoc, inv_mul_eq_one, inv_mul_eq_iff_eq_mul, mul_one] using h
  have hx := PresentedGroup.generated_by (centralPresentation T).relSet _ hg x
  exact (Subgroup.mem_centralizer_singleton_iff.mp hx).symm

theorem dummy₁_central {k μ : ℕ} (T : FP k μ) (x : (centralPresentation T).Group) :
    Commute (centralValue T dummy₁) x := by
  simpa only [perfectification_dummy₁] using
    perfectification_row_central T ⟨μ, by omega⟩ x

theorem dummy₂_central {k μ : ℕ} (T : FP k μ) (x : (centralPresentation T).Group) :
    Commute (centralValue T dummy₂) x := by
  simpa only [perfectification_dummy₂] using
    perfectification_row_central T ⟨μ + 1, by omega⟩ x

theorem centralSection₁_central {k μ : ℕ} (T : FP k μ)
    (x : (centralPresentation T).Group) : Commute (centralValue T centralSection₁) x := by
  simp only [centralValue, centralSection₁, eval_append, eval_power, eval_inverse]
  exact ((dummy₁_central T x).pow_left 32999).mul_left
    ((dummy₂_central T x).pow_left 31999).inv_left

theorem centralSection₂_central {k μ : ℕ} (T : FP k μ)
    (x : (centralPresentation T).Group) : Commute (centralValue T centralSection₂) x := by
  simp only [centralValue, centralSection₂, eval_append, eval_power, eval_inverse]
  exact ((dummy₁_central T x).pow_left 33).inv_left.mul_left
    ((dummy₂_central T x).pow_left 32)

/-- The corrected generators belong to the derived subgroup already at the presentation level. -/
def correctedGenerators {k μ : ℕ} (T : FP k μ) : Fin 2 → (centralPresentation T).Group :=
  ![PresentedGroup.of 0 * (centralValue T centralSection₁)⁻¹,
    PresentedGroup.of 1 * (centralValue T centralSection₂)⁻¹]

theorem abelianization_centralValue {k μ : ℕ} (T : FP k μ) (w : Word 2) :
    Abelianization.of (centralValue T w) =
      eval ![Abelianization.of (PresentedGroup.of 0),
        Abelianization.of (PresentedGroup.of 1)] w := by
  rw [centralValue, map_eval]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem centralSection₁_abelianization {k μ : ℕ} (T : FP k μ) :
    Abelianization.of (centralValue T centralSection₁) =
      Abelianization.of (PresentedGroup.of 0) := by
  rw [abelianization_centralValue, eval_centralSection₁_commutative]

theorem centralSection₂_abelianization {k μ : ℕ} (T : FP k μ) :
    Abelianization.of (centralValue T centralSection₂) =
      Abelianization.of (PresentedGroup.of 1) := by
  rw [abelianization_centralValue, eval_centralSection₂_commutative]

private theorem mul_inv_mem_commutator_of_abelianization {G : Type*} [Group G]
    (a b : G) (h : Abelianization.of b = Abelianization.of a) :
    a * b⁻¹ ∈ commutator G := by
  apply (QuotientGroup.eq_one_iff _).mp
  change Abelianization.of (a * b⁻¹) = 1
  rw [map_mul, map_inv, h, mul_inv_cancel]

private theorem pair_mem {G : Type*} [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) (i : Fin 2) : (![a, b] : Fin 2 → G) i ∈ H := by
  fin_cases i
  · exact ha
  · exact hb

theorem correctedGenerators_mem_commutator {k μ : ℕ} (T : FP k μ) (g : Fin 2) :
    correctedGenerators T g ∈ commutator (centralPresentation T).Group :=
  pair_mem _ _ _
    (mul_inv_mem_commutator_of_abelianization _ _ (centralSection₁_abelianization T))
    (mul_inv_mem_commutator_of_abelianization _ _ (centralSection₂_abelianization T)) g

end SmallPresentationStatements.Conversion
