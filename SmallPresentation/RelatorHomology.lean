module

public import SmallPresentation.SchurQuotientExact
public import SmallPresentation.IdentitySequences

/-!
# Homology exactness for arbitrary attaching relators

The quotient five-term sequence becomes a sequence with a free abelian relator
term whenever identity sequences have balanced exponents. All maps, including
the relator-to-abelianization boundary, are canonical. This theorem is independent
of any particular small-cancellation criterion.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology

open RelationCoordinates

variable {B I : Type} [Group B] (rel : I → B)

/-- The cellular boundary of a relator is its image in the base abelianization. -/
def relatorBoundary : FreeAbelianGroup I →+ H₁ B :=
  FreeAbelianGroup.lift (fun i ↦ Additive.ofMul (Abelianization.of (rel i)))

@[simp] theorem relatorBoundary_of (i : I) :
    relatorBoundary rel (FreeAbelianGroup.of i) = Additive.ofMul (Abelianization.of (rel i)) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem relatorBoundary_coordinates :
    (RelationExtension.boundary (Relations rel)).toAdditive.comp (coordinates rel) =
      relatorBoundary rel := by
  apply FreeAbelianGroup.lift_ext
  intro i
  change (RelationExtension.boundary (Relations rel)).toAdditive
    (coordinates rel (FreeAbelianGroup.of i)) = _
  rw [coordinates_of, relatorBoundary_of]
  rfl

noncomputable def relatorCoordinatesEquiv (h : IdentitySequencesBalanced rel) :
    FreeAbelianGroup I ≃+ Additive (RelationExtension.Kernel (Relations rel)) :=
  AddEquiv.ofBijective (coordinates rel) (coordinates_bijective_of_identity_sequences rel h)

/-- The actual transgression, expressed in the basis of attaching relators. -/
noncomputable def relatorTransgression (h : IdentitySequencesBalanced rel) :
    H₂ (B ⧸ Relations rel) →+ FreeAbelianGroup I :=
  (relatorCoordinatesEquiv rel h).symm.toAddMonoidHom.comp
    (quotientTransgression (Relations rel)).toAdditive

theorem relatorTransgression_ker (h : IdentitySequencesBalanced rel) :
    (relatorTransgression rel h).ker = (map₂ (QuotientGroup.mk' (Relations rel))).range := by
  have hker : ((quotientTransgression (Relations rel)).toAdditive).ker =
      (map₂ (QuotientGroup.mk' (Relations rel))).range := by
    change ((quotientTransgression (Relations rel)).ker).toAddSubgroup =
      ((schurMap (QuotientGroup.mk' (Relations rel))).range).toAddSubgroup
    rw [quotientTransgression_ker]
  rw [← hker]
  ext x
  change (relatorCoordinatesEquiv rel h).symm
    ((quotientTransgression (Relations rel)).toAdditive x) = 0 ↔
      (quotientTransgression (Relations rel)).toAdditive x = 0
  exact (relatorCoordinatesEquiv rel h).symm.map_eq_zero_iff

theorem relatorBoundary_ker (h : IdentitySequencesBalanced rel) :
    (relatorBoundary rel).ker = (relatorTransgression rel h).range := by
  have hrange : ((quotientTransgression (Relations rel)).toAdditive).range =
      ((RelationExtension.boundary (Relations rel)).toAdditive).ker := by
    change ((quotientTransgression (Relations rel)).range).toAddSubgroup =
      ((RelationExtension.boundary (Relations rel)).ker).toAddSubgroup
    rw [quotientTransgression_range]
  apply le_antisymm
  · intro x hx
    have hc : relatorCoordinatesEquiv rel h x ∈
        ((RelationExtension.boundary (Relations rel)).toAdditive).ker := by
      change (RelationExtension.boundary (Relations rel)).toAdditive (coordinates rel x) = 0
      rw [← AddMonoidHom.comp_apply, relatorBoundary_coordinates]
      exact hx
    rw [← hrange] at hc
    obtain ⟨y, hy⟩ := hc
    refine ⟨y, ?_⟩
    change (relatorCoordinatesEquiv rel h).symm
      ((quotientTransgression (Relations rel)).toAdditive y) = x
    rw [hy, AddEquiv.symm_apply_apply]
  · rintro _ ⟨x, rfl⟩
    have hx : (quotientTransgression (Relations rel)).toAdditive x ∈
        ((RelationExtension.boundary (Relations rel)).toAdditive).ker := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    change relatorBoundary rel ((relatorCoordinatesEquiv rel h).symm
      ((quotientTransgression (Relations rel)).toAdditive x)) = 0
    rw [← relatorBoundary_coordinates, AddMonoidHom.comp_apply]
    change (RelationExtension.boundary (Relations rel)).toAdditive
      (relatorCoordinatesEquiv rel h ((relatorCoordinatesEquiv rel h).symm
        ((quotientTransgression (Relations rel)).toAdditive x))) = 0
    rw [AddEquiv.apply_symm_apply]
    exact hx

/-- Exactness at degree one requires only normal generation, not balanced identities. -/
theorem relator_abelian_ker :
    (map₁ (QuotientGroup.mk' (Relations rel))).ker = (relatorBoundary rel).range := by
  change ((RelationExtension.abelianQuotient (Relations rel)).ker).toAddSubgroup = _
  rw [RelationExtension.abelianQuotient_ker]
  rw [← relatorBoundary_coordinates]
  have hs := coordinates_surjective rel
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hs (Additive.ofMul y)
    refine ⟨z, ?_⟩
    change (RelationExtension.boundary (Relations rel)).toAdditive (coordinates rel z) = x
    rw [hz]
    exact hy
  · rintro _ ⟨x, rfl⟩
    exact ⟨(coordinates rel x).toMul, rfl⟩

/-- Full exactness from `H₂(B)` through `H₁(B/N)`, with specified maps. -/
theorem relator_five_term_exact (h : IdentitySequencesBalanced rel) :
    (relatorTransgression rel h).ker = (map₂ (QuotientGroup.mk' (Relations rel))).range ∧
    (relatorBoundary rel).ker = (relatorTransgression rel h).range ∧
    (map₁ (QuotientGroup.mk' (Relations rel))).ker = (relatorBoundary rel).range ∧
    Function.Surjective (map₁ (QuotientGroup.mk' (Relations rel))) :=
  ⟨relatorTransgression_ker rel h, relatorBoundary_ker rel h, relator_abelian_ker rel,
    RelationExtension.abelianQuotient_surjective (Relations rel)⟩

end SmallPresentationStatements.Homology
