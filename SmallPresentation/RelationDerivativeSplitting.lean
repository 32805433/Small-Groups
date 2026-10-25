module

public import SmallPresentation.RelationDerivativeCosets
public import SmallPresentation.RelativeWeightedSplitting

/-! The old summand of a weighted relative presentation is the independent sum
of the factor relation modules over their quotient cosets. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.FactorSplitting

open DirectSum RelationCoordinates
attribute [local instance] Classical.propDecidable

variable {A I : Type} (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a)

abbrev OldIndex := Σ a, (p a).ker

/-- Every relation in a factor, tagged by that factor. -/
def old (r : OldIndex X G p) : FreeGroup (Σ a, X a) :=
  FreeGroup.map (Sigma.mk r.1) r.2.val

variable (new : I → FreeGroup (Σ a, X a))

abbrev all := Sum.elim (old X G p) new
abbrev Relations := RelationCoordinates.Relations (all X G p new)
abbrev Quotient := FreeGroup (Σ a, X a) ⧸ Relations X G p new
abbrev quotient := QuotientGroup.mk' (Relations X G p new)
abbrev Module := RelationAbelianization.Module (Relations X G p new)

/-- Identify the kernel of the quotient map with its specified normal subgroup. -/
def kernelEquiv : (quotient X G p new).ker ≃* Relations X G p new :=
  MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _)

/-- The induced identification of relation abelianizations. -/
def moduleEquiv :
    Additive (Abelianization (quotient X G p new).ker) ≃+ Module X G p new :=
  (MulEquiv.abelianizationCongr (kernelEquiv X G p new)).toAdditive

variable (φ : ∀ a, G a →* Quotient X G p new)
  (compat : ∀ a, (quotient X G p new).comp (FreeGroup.map (Sigma.mk a)) =
    (φ a).comp (p a))
  (C : ∀ a, CosetData (φ a))

/-- The actual independent coset sum, transported into the specified relation subgroup. -/
noncomputable def cosetSum :
    (⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker)) →+ Module X G p new :=
  (moduleEquiv X G p new).toAddMonoidHom.comp
    (cosetRelationSum X G p (quotient X G p new) (QuotientGroup.mk'_surjective _) φ compat C)

/-- Transported factor conjugates are the literal old conjugate-relator classes. -/
theorem moduleEquiv_conjugated_factor_of (a : A) (w : FreeGroup (Σ a, X a))
    (r : (p a).ker) :
    moduleEquiv X G p new
      (relationConjugation (quotient X G p new) w
        (relationMap (p a) (quotient X G p new) (Sigma.mk a) (φ a) (compat a)
          (Additive.ofMul (Abelianization.of r)))) =
      WeightedBasis.conjugateClass (all X G p new) w (Sum.inl ⟨a, r⟩) := by
  change Additive.ofMul (Abelianization.of _) = Additive.ofMul (Abelianization.of _)
  congr 2

/-- Explicit old-coordinate formula for a chosen coset decomposition. -/
theorem cosetSum_of_conjugation (a : A) (c : (C a).Index)
    (v : FreeGroup (X a)) (w : FreeGroup (Σ a, X a))
    (hw : quotient X G p new w = (C a).representative c * φ a (p a v))
    (r : (p a).ker) :
    cosetSum X G p new φ compat C
      (DirectSum.of _ (⟨a, c⟩ : CosetIndex G φ C)
        (relationConjugation (p a) v (Additive.ofMul (Abelianization.of r)))) =
      WeightedBasis.conjugateClass (all X G p new) w (Sum.inl ⟨a, r⟩) := by
  unfold cosetSum
  rw [AddMonoidHom.comp_apply, cosetRelationSum_of_conjugation X G p
    (quotient X G p new) (QuotientGroup.mk'_surjective _) φ compat C a c v w hw]
  exact moduleEquiv_conjugated_factor_of X G p new φ compat a w r

@[simp] theorem oldMap_of (w : FreeGroup (Σ a, X a)) (r : OldIndex X G p) :
    RelativeWeighted.oldMap (old X G p) new
      (FreeAbelianGroup.of (quotient X G p new w, r)) =
      WeightedBasis.conjugateClass (all X G p new) w (Sum.inl r) := by
  simp only [RelativeWeighted.oldMap, AddMonoidHom.comp_apply,
    RelativeWeighted.includeOld, FreeAbelianGroup.map_of_apply]
  exact WeightedBasis.coordinates_of _ _ _

/-- All classes in a factor relation module map into the old-relator image. -/
theorem conjugated_factor_mem_oldMap_range (a : A) (w : FreeGroup (Σ a, X a))
    (z : Additive (Abelianization (p a).ker)) :
    moduleEquiv X G p new
      (relationConjugation (quotient X G p new) w
        (relationMap (p a) (quotient X G p new) (Sigma.mk a) (φ a) (compat a) z)) ∈
      (RelativeWeighted.oldMap (old X G p) new).range := by
  induction z using QuotientGroup.induction_on with
  | H r =>
    refine ⟨FreeAbelianGroup.of (quotient X G p new w, ⟨a, r⟩), ?_⟩
    rw [oldMap_of]
    exact (moduleEquiv_conjugated_factor_of X G p new φ compat a w r).symm

theorem cosetSum_injective (hp : ∀ a, Function.Surjective (p a)) :
    Function.Injective (cosetSum X G p new φ compat C) :=
  (moduleEquiv X G p new).injective.comp
    (cosetRelationSum_injective X G p (quotient X G p new)
      (QuotientGroup.mk'_surjective _) φ compat C hp)

/-- The coset sum realizes precisely the old summand of the weighted splitting. -/
theorem cosetSum_range_eq_oldMap_range (hp : ∀ a, Function.Surjective (p a)) :
    (cosetSum X G p new φ compat C).range =
      (RelativeWeighted.oldMap (old X G p) new).range := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using DirectSum.induction_on with
    | zero => exact AddSubgroup.zero_mem _
    | of i z =>
      unfold cosetSum
      rw [AddMonoidHom.comp_apply, cosetRelationSum_of]
      exact conjugated_factor_mem_oldMap_range X G p new φ compat i.1 _ z
    | add z t hz ht =>
      rw [map_add]
      exact AddSubgroup.add_mem _ hz ht
  · rintro _ ⟨z, rfl⟩
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact AddSubgroup.zero_mem _
    | of v =>
      obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (Relations X G p new) v.1
      rcases v with ⟨v, a, r⟩
      dsimp at hw
      subst v
      erw [oldMap_of]
      obtain ⟨z, hz⟩ := conjugated_factor_mem_cosetRelationSum_range X G p
        (quotient X G p new) (QuotientGroup.mk'_surjective _) φ compat C hp a w
          (Additive.ofMul (Abelianization.of r))
      refine ⟨z, ?_⟩
      unfold cosetSum
      rw [AddMonoidHom.comp_apply, hz]
      exact moduleEquiv_conjugated_factor_of X G p new φ compat a w r
    | neg z hz =>
      rw [map_neg]
      exact AddSubgroup.neg_mem _ hz
    | add z t hz ht =>
      rw [map_add]
      exact AddSubgroup.add_mem _ hz ht

/-- Restrict the coset sum to the old-relator image. -/
noncomputable def cosetSumToOld (hp : ∀ a, Function.Surjective (p a)) :
    (⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker)) →+
      (RelativeWeighted.oldMap (old X G p) new).range :=
  (cosetSum X G p new φ compat C).codRestrict _ (fun z ↦ by
    rw [← cosetSum_range_eq_oldMap_range X G p new φ compat C hp]
    exact ⟨z, rfl⟩)

theorem cosetSumToOld_bijective (hp : ∀ a, Function.Surjective (p a)) :
    Function.Bijective (cosetSumToOld X G p new φ compat C hp) := by
  constructor
  · intro z t he
    exact cosetSum_injective X G p new φ compat C hp (congrArg Subtype.val he)
  · intro z
    have hz := (cosetSum_range_eq_oldMap_range X G p new φ compat C hp).ge z.property
    obtain ⟨t, ht⟩ := hz
    exact ⟨t, Subtype.ext ht⟩

/-- Canonical on actual conjugated factor classes, with coordinates chosen by the cosets. -/
noncomputable def cosetSumEquiv (hp : ∀ a, Function.Surjective (p a)) :
    (⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker)) ≃+
      (RelativeWeighted.oldMap (old X G p) new).range :=
  AddEquiv.ofBijective (cosetSumToOld X G p new φ compat C hp)
    (cosetSumToOld_bijective X G p new φ compat C hp)

/-- The full relation abelianization is the independent old coset sum plus the
free quotient-weighted coordinates of the new attaching relators. -/
noncomputable def splittingEquiv (hp : ∀ a, Function.Surjective (p a))
    (hbalanced : Weighted.Balanced (all X G p new) (quotient X G p new)
      RelativeWeighted.newLabel) :
    ((⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker)) ×
      RelativeWeighted.NewCoordinates (old X G p) new) ≃+ Module X G p new :=
  ((cosetSumEquiv X G p new φ compat C hp).prodCongr (AddEquiv.refl _)).trans
    (RelativeWeighted.splittingEquiv (old X G p) new hbalanced)

@[simp] theorem splittingEquiv_apply (hp : ∀ a, Function.Surjective (p a))
    (hbalanced : Weighted.Balanced (all X G p new) (quotient X G p new)
      RelativeWeighted.newLabel)
    (u : ⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker))
    (v : RelativeWeighted.NewCoordinates (old X G p) new) :
    splittingEquiv X G p new φ compat C hp hbalanced (u, v) =
      cosetSum X G p new φ compat C u + RelativeWeighted.newMap (old X G p) new v := rfl


end SmallPresentationStatements.RelationDerivative.FactorSplitting
