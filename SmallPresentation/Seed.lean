module

public import SmallPresentation.Seed.Abelianization
public import SmallPresentation.UniversalGroup

/-!
# The authorized thirteen-relator universal seed

The upstream source is pinned at `6416dd36ad22f3684583457f234519bafc851396`
in `Seed/Upstream`. The adapter changes only the finite-presentation record;
its word alphabet and the resulting presented group are definitionally equal.
-/
public section

namespace SmallPresentationStatements.Seed

/-- The two-generator thirteen-relator seed, with the exact statement-side interface. -/
theorem exists_two_thirteen_universal : ∃ P : FP 2 13, IsUniversal P.Group := by
  obtain ⟨P, hP⟩ := UniversalGroup.exists_two_generator_thirteen_relator_universal_group
  exact ⟨fromUpstream P, universal_fromUpstream P hP⟩

/-- Choose the literal row recipe used in `Proofs.md`, retaining its coding datum. -/
theorem exists_universal_datum :
    ∃ D : UniversalGroup.CodeWords,
      IsUniversal (fromUpstream (UniversalGroup.Embedding.thirteenPresentation D)).Group := by
  obtain ⟨D, hD⟩ := UniversalGroup.Embedding.exists_universal_datum
  exact ⟨D, universal_fromUpstream _ hD⟩

/-- The same literal thirteen-row seed is universal, normally generated, and has `H₁ = ℤ`. -/
theorem exists_two_thirteen_universal_with_abelianization :
    ∃ P : FP 2 13, IsUniversal P.Group ∧
      Nonempty (Abelianization P.Group ≃* Multiplicative ℤ) ∧
      HasDisplayedNormalGenerator P := by
  obtain ⟨D, hD⟩ := exists_universal_datum
  exact ⟨fromUpstream (UniversalGroup.Embedding.thirteenPresentation D), hD,
    seed_abelianization D, 1, seed_normalGenerator D⟩

end SmallPresentationStatements.Seed
