module

public import SmallPresentation.Assembly

/-!
# Small-presentation theorem assembly

The statements match the protected `SmallPresentationStatements.lean`.
All structural inputs imported by Assembly are proved locally or supplied by the
pinned, checked upstream developments. The four roots are audited using only
propext, Classical.choice and Quot.sound, with no temporary admissions.
-/
public section

namespace SmallPresentationStatements

theorem exists_two_three_universal_with_abelianization_Z :
    ∃ P : FP 2 3,
      IsUniversal P.Group ∧
      Nonempty (Abelianization P.Group ≃* Multiplicative ℤ) ∧
      HasDisplayedNormalGenerator P := by
  obtain ⟨Q, hQ, hU⟩ := three_source
  exact ⟨threePresentation Q 101, hU, threePresentation_abelianization hQ 101,
    threePresentation_hasDisplayedNormalGenerator hQ 101⟩

theorem exists_two_four_universal_adian_rabin_family :
    ∃ A : ℕ → FP 2 4,
      FP.IsAdianRabinFamily A ∧
      ∀ j, ¬ (A j).presentsTrivial → IsUniversal (A j).Group := by
  obtain ⟨Q, hQ, hU⟩ := three_source
  let P := threePresentation Q 101
  have hAb := threePresentation_b_abelianization hQ 101
  have hC := three_cyclicCollapse hQ 101
  have hW := hU.wordProblem_undecidable StructuralObligations.exists_undecidable_word_problem
  refine ⟨fun j ↦ Gordon.presentation P (wordOfNat 2 j),
    Gordon.family_isAdianRabin P hC hW
      (fun w hw ↦ StructuralObligations.gordon_injection P hAb w hw), ?_⟩
  intro j hT
  exact Gordon.universal_of_nontrivial P hC hU
    (fun w hw ↦ StructuralObligations.gordon_injection P hAb w hw) _ hT

theorem exists_torsion_free_two_four_with_abelianization :
    ∃ P : FP 2 4,
      IsMulTorsionFree P.Group ∧
      ¬ ComputablePred P.wordProblem ∧
      Nonempty (Abelianization P.Group ≃* Multiplicative ℤ) ∧
      HasDisplayedNormalGenerator P := by
  obtain ⟨Q, hQ, hT, hW⟩ := four_source
  exact ⟨fourPresentation Q 227, hT, hW, fourPresentation_abelianization hQ 227,
    fourPresentation_hasDisplayedNormalGenerator hQ 227⟩

theorem exists_torsion_free_two_five_adian_rabin_family :
    ∃ A : ℕ → FP 2 5,
      FP.IsAdianRabinFamily A ∧ ∀ j, IsMulTorsionFree (A j).Group := by
  obtain ⟨Q, hQ, hT, hW⟩ := four_source
  let P := fourPresentation Q 227
  have hAb := fourPresentation_b_abelianization hQ 227
  have hC := four_cyclicCollapse hQ 227
  exact ⟨fun j ↦ Gordon.presentation P (wordOfNat 2 j),
    Gordon.family_isAdianRabin P hC hW
      (fun w hw ↦ StructuralObligations.gordon_injection P hAb w hw),
    fun j ↦ Gordon.torsionfree P hC
      (fun w hw ↦ StructuralObligations.gordon_torsionfree P hAb w hw hT) _⟩

end SmallPresentationStatements
