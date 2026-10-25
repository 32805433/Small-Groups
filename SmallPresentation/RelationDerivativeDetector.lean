module

public import SmallPresentation.RelationDerivativeSplitting
public import SmallPresentation.WeightedEquivariance

/-! A conjugation-invariant detector retaining the central relation classes of
all factors and killing the newly attached relators. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

open RelationCoordinates RelationExtension

variable {F : Type} [Group F]

/-- Ambient conjugation acts trivially on the central relation quotient. -/
theorem toCoinvariants_conjugation (N : Subgroup F) [N.Normal] (w : F) (r : N) :
    toCoinvariants N (RelationCoordinates.conjugation N w r) = toCoinvariants N r := by
  apply Subtype.ext
  let π := QuotientGroup.mk' (commutatorKernel N)
  have hc : π r.val * π w = π w * π r.val :=
    kernel_central N (π r.val) (toCoinvariants N r).property (π w)
  change π (w * r.val * w⁻¹) = π r.val
  rw [map_mul, map_mul, map_inv, ← hc, mul_assoc, mul_inv_cancel, mul_one]

variable {X H : Type} [Group H] (p : FreeGroup X →* H)

/-- Pass from the full relation abelianization to its central coinvariants. -/
def centralCoordinates :
    Additive (Abelianization p.ker) →+ Additive (Kernel p.ker) :=
  (Abelianization.lift (toCoinvariants p.ker)).toAdditive

@[simp] theorem centralCoordinates_of (r : p.ker) :
    centralCoordinates p (Additive.ofMul (Abelianization.of r)) =
      Additive.ofMul (toCoinvariants p.ker r) := rfl

/-- Central coinvariants forget ambient conjugation. -/
theorem centralCoordinates_conjugation (w : FreeGroup X)
    (z : Additive (Abelianization p.ker)) :
    centralCoordinates p (relationConjugation p w z) = centralCoordinates p z := by
  induction z using QuotientGroup.induction_on with
  | H r =>
    change Additive.ofMul (toCoinvariants p.ker (kernelConjugation p w r)) =
      Additive.ofMul (toCoinvariants p.ker r)
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change QuotientGroup.mk' (commutatorKernel p.ker) (w * r.val * w⁻¹) =
      QuotientGroup.mk' (commutatorKernel p.ker) r.val
    let π := QuotientGroup.mk' (commutatorKernel p.ker)
    have hc : π r.val * π w = π w * π r.val :=
      kernel_central p.ker (π r.val) (toCoinvariants p.ker r).property (π w)
    change π (w * r.val * w⁻¹) = π r.val
    rw [map_mul, map_mul, map_inv, ← hc, mul_assoc, mul_inv_cancel, mul_one]

end SmallPresentationStatements.RelationDerivative

namespace SmallPresentationStatements.RelationDerivative.FactorSplitting

open DirectSum RelationCoordinates RelationExtension
attribute [local instance] Classical.propDecidable

variable {A I : Type} (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a) (new : I → FreeGroup (Σ a, X a))
  (φ : ∀ a, G a →* Quotient X G p new)
  (compat : ∀ a, (quotient X G p new).comp (FreeGroup.map (Sigma.mk a)) =
    (φ a).comp (p a))
  (C : ∀ a, CosetData (φ a))

abbrev CentralFactors := ⨁ a, Additive (Kernel (p a).ker)

/-- Sum over the coset coordinate and retain the original factor coordinate. -/
noncomputable def collapseCosets :
    (⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker)) →+
      CentralFactors X G p :=
  DirectSum.toAddMonoid (fun i ↦
    (DirectSum.of (fun a ↦ Additive (Kernel (p a).ker)) i.1).comp
      (centralCoordinates (p i.1)))

@[simp] theorem collapseCosets_of (i : CosetIndex G φ C)
    (z : Additive (Abelianization (p i.1).ker)) :
    collapseCosets X G p new φ C (DirectSum.of _ i z) =
      DirectSum.of _ i.1 (centralCoordinates (p i.1) z) :=
  DirectSum.toAddMonoid_of _ _ _

variable (hp : ∀ a, Function.Surjective (p a))
  (hbalanced : Weighted.Balanced (all X G p new) (quotient X G p new)
    RelativeWeighted.newLabel)

/-- Extract the central classes of old factor relations from the full relation module. -/
noncomputable def detector : Module X G p new →+ CentralFactors X G p :=
  (collapseCosets X G p new φ C).comp
    ((AddMonoidHom.fst _ _).comp
      (splittingEquiv X G p new φ compat C hp hbalanced).symm.toAddMonoidHom)

@[simp] theorem detector_splittingEquiv
    (u : ⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker))
    (v : RelativeWeighted.NewCoordinates (old X G p) new) :
    detector X G p new φ compat C hp hbalanced
      (splittingEquiv X G p new φ compat C hp hbalanced (u, v)) =
        collapseCosets X G p new φ C u := by
  change collapseCosets X G p new φ C
    (((splittingEquiv X G p new φ compat C hp hbalanced).symm
      (splittingEquiv X G p new φ compat C hp hbalanced (u, v))).1) = _
  rw [AddEquiv.symm_apply_apply]

/-- Every old conjugate returns its original factor's central relation class. -/
theorem detector_old (w : FreeGroup (Σ a, X a)) (a : A) (r : (p a).ker) :
    detector X G p new φ compat C hp hbalanced
      (WeightedBasis.conjugateClass (all X G p new) w (Sum.inl ⟨a, r⟩)) =
      DirectSum.of _ a (Additive.ofMul (toCoinvariants (p a).ker r)) := by
  obtain ⟨⟨c, g⟩, hc⟩ := (C a).bijective.2 (quotient X G p new w)
  obtain ⟨v, hv⟩ := hp a g
  have hw : quotient X G p new w = (C a).representative c * φ a (p a v) := by
    rw [hv]
    exact hc.symm
  let u := DirectSum.of (fun i : CosetIndex G φ C ↦ Additive (Abelianization (p i.1).ker))
    (⟨a, c⟩ : CosetIndex G φ C)
    (relationConjugation (p a) v (Additive.ofMul (Abelianization.of r)))
  have hu : splittingEquiv X G p new φ compat C hp hbalanced (u, 0) =
      WeightedBasis.conjugateClass (all X G p new) w (Sum.inl ⟨a, r⟩) := by
    rw [splittingEquiv_apply, map_zero, add_zero]
    exact cosetSum_of_conjugation X G p new φ compat C a c v w hw r
  rw [← hu, detector_splittingEquiv]
  change collapseCosets X G p new φ C (DirectSum.of _ _ _) = _
  rw [collapseCosets_of, centralCoordinates_conjugation, centralCoordinates_of]

/-- The new attaching relators contribute no old central relation class. -/
theorem detector_new (w : FreeGroup (Σ a, X a)) (i : I) :
    detector X G p new φ compat C hp hbalanced
      (WeightedBasis.conjugateClass (all X G p new) w (Sum.inr i)) = 0 := by
  let v := FreeAbelianGroup.of (quotient X G p new w, i)
  have hv : splittingEquiv X G p new φ compat C hp hbalanced (0, v) =
      WeightedBasis.conjugateClass (all X G p new) w (Sum.inr i) := by
    rw [splittingEquiv_apply, map_zero, zero_add]
    change WeightedBasis.coordinates (all X G p new)
      (FreeAbelianGroup.of (quotient X G p new w, Sum.inr i)) = _
    exact WeightedBasis.coordinates_of _ _ _
  rw [← hv, detector_splittingEquiv, map_zero]

/-- The detector is invariant under conjugation by every ambient free-group word. -/
theorem detector_conjugation (w : FreeGroup (Σ a, X a)) (z : Module X G p new) :
    detector X G p new φ compat C hp hbalanced
      (RelationAbelianization.conjugationMap (Relations X G p new) w z) =
        detector X G p new φ compat C hp hbalanced z := by
  obtain ⟨v, rfl⟩ := WeightedBasis.coordinates_surjective (all X G p new) z
  have he : ((detector X G p new φ compat C hp hbalanced).comp
      (RelationAbelianization.conjugationMap (Relations X G p new) w)).comp
        (WeightedBasis.coordinates (all X G p new)) =
      (detector X G p new φ compat C hp hbalanced).comp
        (WeightedBasis.coordinates (all X G p new)) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨q, r⟩
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (Relations X G p new) q
    change detector X G p new φ compat C hp hbalanced
      (RelationAbelianization.conjugationMap (Relations X G p new) w
        (WeightedBasis.coordinates (all X G p new)
          (FreeAbelianGroup.of (quotient X G p new f, r)))) = _
    rw [WeightedBasis.coordinates_of, WeightedBasis.conjugationMap_conjugateClass]
    change detector X G p new φ compat C hp hbalanced
      (WeightedBasis.conjugateClass (all X G p new) (w * f) r) =
        detector X G p new φ compat C hp hbalanced
          (WeightedBasis.coordinates (all X G p new)
            (FreeAbelianGroup.of (quotient X G p new f, r)))
    rw [WeightedBasis.coordinates_of]
    rcases r with ⟨a, r⟩ | i
    · rw [detector_old, detector_old]
    · rw [detector_new, detector_new]
  exact DFunLike.congr_fun he v

/-- The invariant detector before abelianizing the target relation subgroup. -/
noncomputable def normalDetector :
    Relations X G p new →* Multiplicative (CentralFactors X G p) :=
  (detector X G p new φ compat C hp hbalanced).toMultiplicative.comp
    (RelationAbelianization.of (Relations X G p new))

theorem normalDetector_conjugation (w : FreeGroup (Σ a, X a))
    (n : Relations X G p new) :
    normalDetector X G p new φ compat C hp hbalanced
      (RelationCoordinates.conjugation (Relations X G p new) w n) =
        normalDetector X G p new φ compat C hp hbalanced n := by
  exact congrArg Multiplicative.ofAdd
    (detector_conjugation X G p new φ compat C hp hbalanced w
      (Additive.ofMul (Abelianization.of n)))

theorem normalDetector_old (w : FreeGroup (Σ a, X a)) (a : A) (r : (p a).ker) :
    normalDetector X G p new φ compat C hp hbalanced
      (RelationCoordinates.conjugation (Relations X G p new) w
        (WeightedBasis.normalRelator (all X G p new) (Sum.inl ⟨a, r⟩))) =
      Multiplicative.ofAdd (DirectSum.of _ a
        (Additive.ofMul (toCoinvariants (p a).ker r))) :=
  congrArg Multiplicative.ofAdd (detector_old X G p new φ compat C hp hbalanced w a r)


end SmallPresentationStatements.RelationDerivative.FactorSplitting
