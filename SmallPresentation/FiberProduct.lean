module

public import SmallPresentation.Computability

/-!
# Finite generators for the quotient fiber product

The diagonal generators and left relators generate precisely the pairs with
equal quotient images. This proves the fiber-product membership calculation
used by the torsion-free detector, without importing it as an external theorem.
-/
@[expose] public section

namespace SmallPresentationStatements.FiberProduct

variable {F : Type*} [Group F]

def diagonal : F →* F × F where
  toFun x := (x, x)
  map_one' := rfl
  map_mul' _ _ := rfl

def left : F →* F × F where
  toFun x := (x, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

def generated (S R : Set F) : Subgroup (F × F) :=
  Subgroup.closure (diagonal '' S ∪ left '' R)

theorem diagonal_mem (S R : Set F) (hS : Subgroup.closure S = ⊤) (x : F) :
    diagonal x ∈ generated S R := by
  have h : Subgroup.closure S ≤ (generated S R).comap diagonal := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    exact Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  apply h
  rw [hS]
  trivial

theorem left_normalClosure_mem (S R : Set F) (hS : Subgroup.closure S = ⊤)
    {x : F} (hx : x ∈ Subgroup.normalClosure R) : left x ∈ generated S R := by
  let K := (generated S R).comap left
  have hK : K.Normal := by
    constructor
    intro a ha b
    have h := (generated S R).mul_mem
      ((generated S R).mul_mem (diagonal_mem S R hS b) ha)
      ((generated S R).inv_mem (diagonal_mem S R hS b))
    change left (b * a * b⁻¹) ∈ generated S R
    simpa [diagonal, left] using h
  have hR : R ⊆ K := by
    intro a ha
    exact Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩)
  exact Subgroup.normalClosure_le_normal hR hx

def equalizer (R : Set F) : Subgroup (F × F) where
  carrier := {x | QuotientGroup.mk' (Subgroup.normalClosure R) x.1 =
    QuotientGroup.mk' (Subgroup.normalClosure R) x.2}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change QuotientGroup.mk' _ (x.1 * y.1) = QuotientGroup.mk' _ (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change QuotientGroup.mk' _ x.1⁻¹ = QuotientGroup.mk' _ x.2⁻¹
    rw [map_inv, map_inv, hx]

theorem generated_eq_equalizer (S R : Set F) (hS : Subgroup.closure S = ⊤) :
    generated S R = equalizer R := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · rfl
    · change QuotientGroup.mk' (Subgroup.normalClosure R) x =
        QuotientGroup.mk' (Subgroup.normalClosure R) 1
      rw [map_one]
      exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.subset_normalClosure hx)
  · rintro ⟨u, v⟩ huv
    have hrel : u * v⁻¹ ∈ Subgroup.normalClosure R := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (Subgroup.normalClosure R) (u * v⁻¹) = 1
      rw [map_mul, map_inv, show QuotientGroup.mk' (Subgroup.normalClosure R) u =
        QuotientGroup.mk' (Subgroup.normalClosure R) v from huv, mul_inv_cancel]
    have h := (generated S R).mul_mem (left_normalClosure_mem S R hS hrel)
      (diagonal_mem S R hS v)
    simpa [left, diagonal] using h

theorem left_mem_iff (S R : Set F) (hS : Subgroup.closure S = ⊤) (w : F) :
    left w ∈ generated S R ↔ w ∈ Subgroup.normalClosure R := by
  rw [generated_eq_equalizer S R hS]
  change QuotientGroup.mk' (Subgroup.normalClosure R) w =
    QuotientGroup.mk' (Subgroup.normalClosure R) 1 ↔ _
  rw [map_one]
  exact QuotientGroup.eq_one_iff w

def presentationSubgroup {n m : ℕ} (P : FP n m) :
    Subgroup (FreeGroup (Fin n) × FreeGroup (Fin n)) :=
  generated (Set.range FreeGroup.of) P.relSet

theorem presentation_mem_iff {n m : ℕ} (P : FP n m) (u v : FreeGroup (Fin n)) :
    (u, v) ∈ presentationSubgroup P ↔ PresentedGroup.mk P.relSet u =
      PresentedGroup.mk P.relSet v := by
  rw [presentationSubgroup, generated_eq_equalizer _ _ (FreeGroup.closure_range_of (Fin n))]
  rfl

theorem detector_mem_iff {n m : ℕ} (P : FP n m) (w : Word n) :
    (FreeGroup.mk w, 1) ∈ presentationSubgroup P ↔ P.wordProblem w := by
  rw [presentation_mem_iff, map_one]
  rfl

end SmallPresentationStatements.FiberProduct
