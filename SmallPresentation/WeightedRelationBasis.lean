module

public import SmallPresentation.WeightedIdentitySequences
public import SmallPresentation.RelationAbelianization

/-!
# A free relation-module basis from weighted identities

The condition on identities is stated before taking either abelianization or
coinvariants. It implies that the actual conjugated attaching relators give a
basis of the full relation abelianization, with quotient-indexed coordinates.
-/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.WeightedBasis

variable {F I : Type} [Group F] (rel : I → F)

abbrev Quotient := F ⧸ Relations rel
abbrev Module := RelationAbelianization.Module (Relations rel)
abbrev Coordinates := FreeAbelianGroup (Quotient rel × I)

/-- The attaching relator as an element of its normal closure. -/
def normalRelator (i : I) : Relations rel :=
  ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩

/-- The class of an actual conjugate of an attaching relator. -/
def conjugateClass (f : F) (i : I) : Module rel :=
  Additive.ofMul (Abelianization.of (conjugation (Relations rel) f (normalRelator rel i)))

theorem conjugateClass_eq (f g : F) (i : I)
    (h : QuotientGroup.mk' (Relations rel) f = QuotientGroup.mk' (Relations rel) g) :
    conjugateClass rel f i = conjugateClass rel g i := by
  exact DFunLike.congr_fun (RelationAbelianization.conjugationMap_eq (Relations rel) f g h)
    (Additive.ofMul (Abelianization.of (normalRelator rel i)))

/-- Canonical relation coordinates, using any representative of the quotient element. -/
noncomputable def coordinates : Coordinates rel →+ Module rel :=
  FreeAbelianGroup.lift (fun x ↦ conjugateClass rel
    (RelationAbelianization.representative (Relations rel) x.1) x.2)

@[simp] theorem coordinates_of (f : F) (i : I) :
    coordinates rel (FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) f, i)) =
      conjugateClass rel f i := by
  rw [coordinates, FreeAbelianGroup.lift_apply_of]
  exact conjugateClass_eq rel _ _ _ (RelationAbelianization.representative_spec _ _)

/-- The image of a formal conjugate word in the relation abelianization. -/
def abelianEvaluation : FreeGroup (F × I) →* Multiplicative (Module rel) :=
  Abelianization.of.comp (normalEvaluation rel)

@[simp] theorem abelianEvaluation_of (f : F) (i : I) :
    abelianEvaluation rel (FreeGroup.of (f, i)) =
      Multiplicative.ofAdd (conjugateClass rel f i) := by
  change Abelianization.of (normalEvaluation rel (FreeGroup.of (f, i))) =
    Abelianization.of (conjugation (Relations rel) f (normalRelator rel i))
  congr 1
  apply Subtype.ext
  change conjugateEvaluation rel (FreeGroup.of (f, i)) = f * rel i * f⁻¹
  simp [conjugateEvaluation]

/-- All relation classes are represented by finite words of conjugates. -/
theorem abelianEvaluation_surjective : Function.Surjective (abelianEvaluation rel) := by
  intro x
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (commutator (Relations rel)) x.toAdd.toMul
  obtain ⟨w, hw⟩ := normalEvaluation_surjective rel n
  exact ⟨w, by change Abelianization.of (normalEvaluation rel w) = x; rw [hw]; exact hn⟩

/-- Coordinates evaluate the same formal conjugates as the quotient-weighted vector. -/
theorem coordinates_vector :
    (coordinates rel).toMultiplicative.comp
      (Weighted.vector (QuotientGroup.mk' (Relations rel)) (some : I → Option I)) =
      abelianEvaluation rel := by
  apply FreeGroup.ext_hom
  rintro ⟨f, i⟩
  change Multiplicative.ofAdd (coordinates rel
    (FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) f, i))) = _
  rw [coordinates_of]
  exact (abelianEvaluation_of rel f i).symm

/-- Surjectivity uses only normal generation, not weighted independence. -/
theorem coordinates_surjective : Function.Surjective (coordinates rel) := by
  intro x
  obtain ⟨w, hw⟩ := abelianEvaluation_surjective rel (Multiplicative.ofAdd x)
  refine ⟨(Weighted.vector (QuotientGroup.mk' (Relations rel))
    (some : I → Option I) w).toAdd, ?_⟩
  have h := DFunLike.congr_fun (coordinates_vector rel) w
  exact congrArg Multiplicative.toAdd (h.trans hw)

variable (h : Weighted.Balanced rel (QuotientGroup.mk' (Relations rel))
  (some : I → Option I))

/-- The inverse basis map is induced by weighted identities. -/
noncomputable def inverseCoordinates : Module rel →+ Coordinates rel :=
  (Weighted.abelianCoordinates rel (QuotientGroup.mk' (Relations rel))
    (some : I → Option I) h).toAdditive

@[simp] theorem inverseCoordinates_conjugateClass (f : F) (i : I) :
    inverseCoordinates rel h (conjugateClass rel f i) =
      FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) f, i) := by
  change (Weighted.normalCoordinates rel (QuotientGroup.mk' (Relations rel)) some h
    (conjugation (Relations rel) f (normalRelator rel i))).toAdd = _
  rw [Weighted.normalCoordinates_conjugation]
  change (Weighted.shift (QuotientGroup.mk' (Relations rel) f))
    ((Weighted.normalCoordinates rel (QuotientGroup.mk' (Relations rel)) some h
      (normalRelator rel i)).toAdd) = _
  rw [normalRelator, Weighted.normalCoordinates_relator]
  simp [Weighted.generator]

theorem inverseCoordinates_comp :
    (inverseCoordinates rel h).comp (coordinates rel) = AddMonoidHom.id _ := by
  apply FreeAbelianGroup.lift_ext
  rintro ⟨q, i⟩
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (Relations rel) q
  change inverseCoordinates rel h (coordinates rel
    (FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) f, i))) = _
  rw [coordinates_of, inverseCoordinates_conjugateClass]
  rfl

/-- The actual conjugate-relator coordinates form a basis of the relation module. -/
noncomputable def equiv : Coordinates rel ≃+ Module rel :=
  AddEquiv.ofBijective (coordinates rel)
    ⟨Function.LeftInverse.injective (g := inverseCoordinates rel h)
      (fun x ↦ DFunLike.congr_fun (inverseCoordinates_comp rel h) x),
      coordinates_surjective rel⟩

@[simp] theorem equiv_of (f : F) (i : I) :
    equiv rel h (FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) f, i)) =
      conjugateClass rel f i := coordinates_of rel f i

end SmallPresentationStatements.RelationCoordinates.WeightedBasis
