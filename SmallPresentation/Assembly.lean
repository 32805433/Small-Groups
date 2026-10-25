module

public import SmallPresentation.StructuralObligations
public import SmallPresentation.Seed

/-! # Assembly of the source groups and effective families -/
@[expose] public section

namespace SmallPresentationStatements

open StructuralObligations

theorem universal_seed : ∃ P : FP 2 13,
    IsUniversal P.Group ∧ Nonempty (Abelianization P.Group ≃* Multiplicative ℤ) := by
  obtain ⟨D, hD⟩ := Seed.exists_universal_datum
  exact ⟨_, hD, seed_abelianization D⟩

theorem three_source : ∃ Q : FP 2 84,
    Normalized Q ∧ IsUniversal (threePresentation Q 101).Group := by
  obtain ⟨P, hP, hAb⟩ := universal_seed
  obtain ⟨Q, hQ, hC, hN, f, hf⟩ := universal_conversion P hP hAb
  obtain ⟨g, hg⟩ := three_packing Q hQ hC hN
  exact ⟨Q, hQ, (hP.of_injective f hf).of_injective g hg⟩

theorem four_source : ∃ Q : FP 2 216, Normalized Q ∧
    IsMulTorsionFree (fourPresentation Q 227).Group ∧
    ¬ ComputablePred (fourPresentation Q 227).wordProblem := by
  obtain ⟨P, hP, hAb⟩ := universal_seed
  have hWP := hP.wordProblem_undecidable exists_undecidable_word_problem
  obtain ⟨Q, hQ, hC, hN, hT, hWQ⟩ := torsionfree_conversion P hWP hAb
  obtain ⟨⟨f, hf⟩, hTF⟩ := four_packing Q hQ hC hN hT
  exact ⟨Q, hQ, hTF, FP.wordProblem_undecidable_of_injective f hf hWQ⟩

end SmallPresentationStatements
