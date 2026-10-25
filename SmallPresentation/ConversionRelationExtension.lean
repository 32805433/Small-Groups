module

public import SmallPresentation.ConversionIdentification
public import SmallPresentation.RelationExtension
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The literal central presentation is the standard relation extension -/
@[expose] public section

namespace SmallPresentationStatements.Conversion
open Word
open scoped commutatorElement

variable {k μ : ℕ}

abbrev perfectificationRelations (T : FP k μ) : Subgroup (FreeGroup (Fin 2)) :=
  Subgroup.normalClosure (perfectification T).relSet

private theorem eval_free {n : ℕ} (w : Word n) :
    eval FreeGroup.of w = FreeGroup.mk w := FreeGroup.lift_of_apply _

private theorem mk_word_commutator {n : ℕ} (i : Fin n) (w : Word n) :
    FreeGroup.mk (Word.commutator (gen i) w) =
      ⁅(FreeGroup.of i)⁻¹, (FreeGroup.mk w)⁻¹⁆ := by
  rw [← eval_free, eval_commutator, eval_gen, eval_free]
  simp only [commutatorElement_def, inv_inv]

/-- The normal closure of the printed commutation rows is exactly `[R,F]`. -/
theorem centralPresentation_relations (T : FP k μ) :
    Subgroup.normalClosure (centralPresentation T).relSet =
      RelationExtension.commutatorKernel (perfectificationRelations T) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    change FreeGroup.mk (Word.commutator _ _) ∈ _
    rw [mk_word_commutator, RelationExtension.commutatorKernel, Subgroup.commutator_comm]
    apply Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    apply Subgroup.inv_mem
    exact Subgroup.subset_normalClosure ⟨_, rfl⟩
  · let π := PresentedGroup.mk (centralPresentation T).relSet
    have hcenter : perfectificationRelations T ≤
        (Subgroup.center (centralPresentation T).Group).comap π := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨j, rfl⟩
      change π (FreeGroup.mk ((perfectification T).relator j)) ∈
        Subgroup.center (centralPresentation T).Group
      change PresentedGroup.mk (centralPresentation T).relSet
        (FreeGroup.mk ((perfectification T).relator j)) ∈
        Subgroup.center (centralPresentation T).Group
      rw [← (centralPresentation T).eval_of]
      exact Subgroup.mem_center_iff.mpr fun x ↦ (perfectification_row_central T j x).symm
    apply Subgroup.commutator_le.mpr
    intro r hr f _
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp (hcenter hr) (π f)).symm

/-- The actual printed `M` is `F/[R,F]`, with no presentation-size assumption. -/
def centralEquivRelationExtension (T : FP k μ) :
    (centralPresentation T).Group ≃* RelationExtension.Total (perfectificationRelations T) :=
  QuotientGroup.quotientMulEquivOfEq (centralPresentation_relations T)

/-- The complete local normalization calculation, with the standard relation extension
as target. A generic universal-central-extension theorem can now be applied directly. -/
def normalizedEquivRelationDerived (T : FP k μ) :
    (normalizedPresentation T).Group ≃*
      commutator (RelationExtension.Total (perfectificationRelations T)) :=
  (normalizedEquivDerived T).trans
    (((centralEquivRelationExtension T).subgroupMap _).trans
      (MulEquiv.subgroupCongr
        (map_commutator_of_surjective (centralEquivRelationExtension T).surjective)))

/-- The displayed normalized presentation maps onto the actual perfectification. -/
def normalizedProjection (T : FP k μ) :
    (normalizedPresentation T).Group →* (perfectification T).Group :=
  ((RelationExtension.projection (perfectificationRelations T)).comp
    (commutator (RelationExtension.Total (perfectificationRelations T))).subtype).comp
      (normalizedEquivRelationDerived T).toMonoidHom

theorem normalizedProjection_surjective (T : FP k μ) :
    Function.Surjective (normalizedProjection T) := by
  have h : Function.Surjective
      ((RelationExtension.projection (perfectificationRelations T)).comp
        (commutator (RelationExtension.Total (perfectificationRelations T))).subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      map_commutator_of_surjective (RelationExtension.projection_surjective _)]
    exact perfectification_commutator_eq_top T
  exact h.comp (normalizedEquivRelationDerived T).surjective

private theorem central_kernel_comp_injective {A B C : Type*} [Group A] [Group B] [Group C]
    (i : A →* B) (hi : Function.Injective i) (π : B →* C)
    (hπ : ∀ z ∈ π.ker, ∀ x : B, z * x = x * z) :
    ∀ z ∈ (π.comp i).ker, ∀ x : A, z * x = x * z := by
  intro z hz x
  apply hi
  simp only [map_mul]
  exact hπ (i z) hz (i x)

theorem normalizedProjection_kernel_central (T : FP k μ) :
    ∀ z ∈ (normalizedProjection T).ker,
      ∀ x : (normalizedPresentation T).Group, z * x = x * z :=
  central_kernel_comp_injective
    ((commutator (RelationExtension.Total (perfectificationRelations T))).subtype.comp
      (normalizedEquivRelationDerived T).toMonoidHom)
    (Subtype.val_injective.comp (normalizedEquivRelationDerived T).injective)
    _ (RelationExtension.kernel_central _)

end SmallPresentationStatements.Conversion
