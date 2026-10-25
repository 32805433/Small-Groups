module

public import SmallPresentation.CentralExtensionSplitting
public import Mathlib.Algebra.Module.Projective

/-! Central-extension lifting over groups with projective integral
abelianization. Free abelianizations satisfy this hypothesis automatically. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable (G : Type) [Group G]

theorem canonicalAbelianQuotient_split [Module.Projective ℤ (H₁ G)] :
    ∃ s : Abelianization G →* Abelianization (FreeGroup G),
      (canonicalAbelianQuotient G).comp s = MonoidHom.id _ := by
  let q := (canonicalAbelianQuotient G).toAdditive.toIntLinearMap
  obtain ⟨s,hs⟩ := Module.projective_lifting_property q
    (LinearMap.id : H₁ G →ₗ[ℤ] H₁ G) (canonicalAbelianQuotient_surjective G)
  refine ⟨s.toAddMonoidHom.toMultiplicative, ?_⟩
  apply MonoidHom.ext
  intro x
  exact LinearMap.congr_fun hs (Additive.ofMul x)

variable {G} {E Q : Type} [Group E] [Group Q]

/-- Vanishing of the Hopf obstruction suffices for lifting when the source
abelianization is projective; the lift preserves the given derived lift. -/
theorem centralLift_of_hopf_zero [Module.Projective ℤ (H₁ G)]
    (π : E →* Q) (hc : UniversalCentralExtension.Central π) (f : G →* Q)
    (σ : CanonicalTotal G →* E) (hσ : π.comp σ = f.comp (totalEvaluation G))
    (hzero : ∀ x : Schur G, σ x.1.1 = 1) :
    ∃ l : G →* E, π.comp l = f ∧
      ∀ x : CanonicalTotal G, x ∈ commutator (CanonicalTotal G) →
        l (totalEvaluation G x) = σ x := by
  obtain ⟨s,hs⟩ := canonicalAbelianQuotient_split G
  exact centralLift_of_hopf_zero_of_split s hs π hc f σ hσ hzero

theorem centralSection_of_hopf_zero [Module.Projective ℤ (H₁ G)]
    (π : E →* G) (hc : UniversalCentralExtension.Central π)
    (σ : CanonicalTotal G →* E) (hσ : π.comp σ = totalEvaluation G)
    (hzero : ∀ x : Schur G, σ x.1.1 = 1) :
    ∃ l : G →* E, π.comp l = MonoidHom.id G := by
  obtain ⟨l,hl,_⟩ := centralLift_of_hopf_zero π hc (MonoidHom.id G) σ
    (by simpa using hσ) hzero
  exact ⟨l,hl⟩

end SmallPresentationStatements.Homology
