module

public import SmallPresentation.RelationDerivativeDetector
public import SmallPresentation.RelativeHopfDetector
public import SmallPresentation.FreeProductPresentation

/-! Actual degree-two homology injection for a quotient of a free product,
derived from weighted relative identity reduction and embedded factors. All
presentations in this theorem are the canonical free presentations of the factors. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.CanonicalSchur

open DirectSum RelationCoordinates RelationExtension
open Homology
attribute [local instance] Classical.propDecidable

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]

abbrev factorProjection (a : A) := freeProjection (G a)
abbrev SourceRelations := FreeProductPresentation.Relations G
abbrev OldIndex := FactorSplitting.OldIndex G G (factorProjection G)
abbrev old := FactorSplitting.old G G (factorProjection G)

variable (new : I → FreeGroup (Σ a, G a))

abbrev all := FactorSplitting.all G G (factorProjection G) new
abbrev TargetRelations := FactorSplitting.Relations G G (factorProjection G) new
abbrev Target := FactorSplitting.Quotient G G (factorProjection G) new
abbrev quotient := FactorSplitting.quotient G G (factorProjection G) new

/-- Canonical factor relations normally generate the source presentation kernel. -/
theorem sourceRelations_eq : SourceRelations G = Relations (old G) := by
  change FreeProductPresentation.Relations G = Subgroup.normalClosure (Set.range (old G))
  rw [FreeProductPresentation.relations_eq_normalClosure]
  rfl

/-- Adding the new relators enlarges the old presentation kernel. -/
theorem source_le_target : SourceRelations G ≤ TargetRelations G new := by
  rw [sourceRelations_eq]
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨r, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inl r, rfl⟩

/-- Evaluate arbitrary conjugates of the old factor relations in the source kernel. -/
def sourceEvaluation : FreeGroup (FreeGroup (Σ a, G a) × OldIndex G) →* SourceRelations G :=
  (MulEquiv.subgroupCongr (sourceRelations_eq G).symm).toMonoidHom.comp
    (normalEvaluation (old G))

@[simp] theorem sourceEvaluation_of (w : FreeGroup (Σ a, G a)) (r : OldIndex G) :
    (sourceEvaluation G (FreeGroup.of (w, r))).val = w * old G r * w⁻¹ := by
  change (normalEvaluation (old G) (FreeGroup.of (w, r))).val = _
  simp [normalEvaluation, conjugateEvaluation]

theorem sourceEvaluation_surjective : Function.Surjective (sourceEvaluation G) :=
  (MulEquiv.subgroupCongr (sourceRelations_eq G).symm).surjective.comp
    (normalEvaluation_surjective (old G))

variable (φ : ∀ a, G a →* Target G new)
  (compat : ∀ a, (quotient G new).comp (FreeGroup.map (Sigma.mk a)) =
    (φ a).comp (factorProjection G a))
  (hφ : ∀ a, Function.Injective (φ a))
  (hbalanced : Weighted.Balanced (all G new) (quotient G new) RelativeWeighted.newLabel)

theorem factorProjection_surjective (a : A) :
    Function.Surjective (factorProjection G a) :=
  fun g ↦ ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩

/-- The detector into the central relation kernel of the source free product. -/
noncomputable def sourceDetector : TargetRelations G new →* Kernel (SourceRelations G) :=
  (FreeProductPresentation.relationSum G).toMultiplicativeLeft.comp
    (FactorSplitting.normalDetector G G (factorProjection G) new φ compat
      (fun a ↦ cosetDataOfInjective (φ a) (hφ a))
      (factorProjection_surjective G) hbalanced)

theorem sourceDetector_conjugation (w : FreeGroup (Σ a, G a))
    (n : TargetRelations G new) :
    sourceDetector G new φ compat hφ hbalanced (conjugation (TargetRelations G new) w n) =
      sourceDetector G new φ compat hφ hbalanced n := by
  unfold sourceDetector
  rw [MonoidHom.comp_apply, FactorSplitting.normalDetector_conjugation]
  rfl

/-- The detector recovers the actual central class of every old relation. -/
theorem sourceDetector_recovers (n : SourceRelations G) :
    sourceDetector G new φ compat hφ hbalanced
      ⟨n.val, source_le_target G new n.property⟩ = toCoinvariants (SourceRelations G) n := by
  obtain ⟨w, rfl⟩ := sourceEvaluation_surjective G n
  let incl : SourceRelations G →* TargetRelations G new :=
    Subgroup.inclusion (source_le_target G new)
  have he : ((sourceDetector G new φ compat hφ hbalanced).comp incl).comp
      (sourceEvaluation G) = (toCoinvariants (SourceRelations G)).comp (sourceEvaluation G) := by
    apply FreeGroup.ext_hom
    rintro ⟨f, a, r⟩
    simp only [MonoidHom.comp_apply]
    let s : SourceRelations G :=
      ⟨old G ⟨a, r⟩, FreeProductPresentation.factor_relations G a r.property⟩
    have heval : sourceEvaluation G (FreeGroup.of (f, ⟨a, r⟩)) =
        conjugation (SourceRelations G) f s := by
      apply Subtype.ext
      exact sourceEvaluation_of G f ⟨a, r⟩
    rw [heval]
    change sourceDetector G new φ compat hφ hbalanced
      (conjugation (TargetRelations G new) f
        (WeightedBasis.normalRelator (all G new) (Sum.inl ⟨a, r⟩))) = _
    unfold sourceDetector
    rw [MonoidHom.comp_apply, FactorSplitting.normalDetector_old]
    change (FreeProductPresentation.relationSum G
      (DirectSum.of _ a (Additive.ofMul (toCoinvariants (canonicalRelations (G a)) r)))).toMul = _
    rw [FreeProductPresentation.relationSum_of]
    change toCoinvariants (SourceRelations G) s =
      toCoinvariants (SourceRelations G) (conjugation (SourceRelations G) f s)
    exact (toCoinvariants_conjugation (SourceRelations G) f s).symm
  exact DFunLike.congr_fun he w

include compat in
/-- The quotient of the disjoint free presentation agrees with the actual free-product map. -/
theorem quotient_commutes :
    (quotient G new).comp (MonoidHom.id _) =
      (Monoid.CoprodI.lift φ).comp (FreeProductPresentation.projection G) := by
  apply FreeGroup.ext_hom
  rintro ⟨a, g⟩
  have hc := DFunLike.congr_fun (compat a) (FreeGroup.of g)
  simpa [FreeProductPresentation.projection, factorProjection, freeProjection] using hc

include compat hφ hbalanced in
/-- Weighted relative identity reduction and factor embeddings imply injectivity
of the actual free-product homomorphism on degree-two homology. -/
theorem map₂_lift_injective : Function.Injective (Homology.map₂ (Monoid.CoprodI.lift φ)) := by
  exact Homology.map₂_injective_of_relationDetector
    (SourceRelations G) (TargetRelations G new) (MonoidHom.id _)
    (source_le_target G new)
    (FreeProductPresentation.projection G) (quotient G new)
    (FreeProductPresentation.projection_surjective G) (QuotientGroup.mk'_surjective _)
    rfl (QuotientGroup.ker_mk' _) (Monoid.CoprodI.lift φ)
    (quotient_commutes G new φ compat)
    (sourceDetector G new φ compat hφ hbalanced)
    (sourceDetector_conjugation G new φ compat hφ hbalanced)
    (sourceDetector_recovers G new φ compat hφ hbalanced)

end SmallPresentationStatements.RelationDerivative.CanonicalSchur
