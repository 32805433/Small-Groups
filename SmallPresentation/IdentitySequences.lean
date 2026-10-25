module

public import SmallPresentation.RelationCoordinates

/-! Identity sequences and central relation coordinates for arbitrary groups.
A word in conjugates of the defining relators carries its evaluation and its vector
of relator exponents. Vanishing of the exponent vector on every identity sequence
is the precise algebraic input needed for independence of central relation coordinates. -/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates

open RelationExtension

variable {F I : Type} [Group F] (rel : I → F)

/-- Evaluate a word whose letters specify a conjugator and a relator. -/
def conjugateEvaluation : FreeGroup (F × I) →* F :=
  FreeGroup.lift (fun p ↦ p.1 * rel p.2 * p.1⁻¹)

/-- The total exponent of each relator in a word of conjugates. -/
def exponentVector : FreeGroup (F × I) →* Multiplicative (FreeAbelianGroup I) :=
  FreeGroup.lift (fun p ↦ Multiplicative.ofAdd (FreeAbelianGroup.of p.2))

/-- An identity sequence has zero exponent of each defining relator. This is a
condition on ordinary words and their evaluations, without reference to homology
or the central relation quotient. -/
def IdentitySequencesBalanced : Prop :=
  (conjugateEvaluation rel).ker ≤ (exponentVector (F := F) (I := I)).ker

theorem conjugateEvaluation_range : (conjugateEvaluation rel).range = Relations rel := by
  rw [conjugateEvaluation, FreeGroup.range_lift_eq_closure]
  unfold Relations Subgroup.normalClosure
  congr 1
  ext x
  constructor
  · rintro ⟨⟨f, i⟩, rfl⟩
    exact Group.mem_conjugatesOfSet_iff.mpr
      ⟨rel i, ⟨i, rfl⟩, isConj_iff.mpr ⟨f, rfl⟩⟩
  · intro hx
    obtain ⟨r, ⟨i, rfl⟩, h⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨f, hf⟩ := isConj_iff.mp h
    exact ⟨(f, i), hf⟩

/-- The evaluation map, with codomain restricted to the normal closure. -/
def normalEvaluation : FreeGroup (F × I) →* Relations rel :=
  (conjugateEvaluation rel).codRestrict (Relations rel) (fun w ↦ by
    rw [← conjugateEvaluation_range]
    exact ⟨w, rfl⟩)

theorem normalEvaluation_surjective : Function.Surjective (normalEvaluation rel) := by
  intro n
  have hn : n.val ∈ (conjugateEvaluation rel).range := by
    rw [conjugateEvaluation_range]
    exact n.property
  obtain ⟨w, hw⟩ := hn
  exact ⟨w, Subtype.ext hw⟩

/-- Multiplying all conjugators on the left realizes ambient conjugation. -/
def conjugatorShift (f : F) : FreeGroup (F × I) →* FreeGroup (F × I) :=
  FreeGroup.map (fun p ↦ (f * p.1, p.2))

theorem evaluation_shift (f : F) (w : FreeGroup (F × I)) :
    normalEvaluation rel (conjugatorShift f w) =
      conjugation (Relations rel) f (normalEvaluation rel w) := by
  have h : (normalEvaluation rel).comp (conjugatorShift f) =
      (conjugation (Relations rel) f).comp (normalEvaluation rel) := by
    apply FreeGroup.ext_hom
    rintro ⟨g, i⟩
    apply Subtype.ext
    simp [normalEvaluation, conjugateEvaluation, conjugatorShift, conjugation, mul_assoc]
  exact DFunLike.congr_fun h w

theorem exponentVector_shift (f : F) (w : FreeGroup (F × I)) :
    exponentVector (conjugatorShift f w) = exponentVector w := by
  have h : (exponentVector (F := F) (I := I)).comp (conjugatorShift f) =
      exponentVector := by
    apply FreeGroup.ext_hom
    rintro ⟨g, i⟩
    simp [exponentVector, conjugatorShift]
  exact DFunLike.congr_fun h w

/-- Balanced identity sequences make the exponent vector independent of the chosen
expression of a normal-subgroup element as a product of conjugates. -/
noncomputable def identityExponents (h : IdentitySequencesBalanced rel) :
    Relations rel →* Multiplicative (FreeAbelianGroup I) :=
  (normalEvaluation rel).liftOfSurjective (normalEvaluation_surjective rel)
    ⟨exponentVector, fun w hw ↦ h (show w ∈ (conjugateEvaluation rel).ker from
      congrArg Subtype.val hw)⟩

@[simp] theorem identityExponents_evaluation (h : IdentitySequencesBalanced rel)
    (w : FreeGroup (F × I)) : identityExponents rel h (normalEvaluation rel w) =
      exponentVector w := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem identityExponents_conjugation (h : IdentitySequencesBalanced rel)
    (f : F) (n : Relations rel) :
    identityExponents rel h (conjugation (Relations rel) f n) = identityExponents rel h n := by
  obtain ⟨w, rfl⟩ := normalEvaluation_surjective rel n
  rw [← evaluation_shift, identityExponents_evaluation, identityExponents_evaluation,
    exponentVector_shift]

theorem identityExponents_relator (h : IdentitySequencesBalanced rel) (i : I) :
    identityExponents rel h ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩ =
      Multiplicative.ofAdd (FreeAbelianGroup.of i) := by
  have hr : (⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩ : Relations rel) =
      normalEvaluation rel (FreeGroup.of (1, i)) := by
    apply Subtype.ext
    simp [normalEvaluation, conjugateEvaluation]
  rw [hr, identityExponents_evaluation]
  simp [exponentVector]

/-- The inverse central coordinates are induced by the exponent vector. -/
noncomputable def identityInverseCoordinates (h : IdentitySequencesBalanced rel) :
    Additive (Kernel (Relations rel)) →+ FreeAbelianGroup I :=
  (liftInvariant (Relations rel) (identityExponents rel h)
    (identityExponents_conjugation rel h)).toAdditiveLeft

theorem identityInverseCoordinates_comp (h : IdentitySequencesBalanced rel) :
    (identityInverseCoordinates rel h).comp (coordinates rel) =
      AddMonoidHom.id (FreeAbelianGroup I) := by
  apply FreeAbelianGroup.lift_ext
  intro i
  change identityInverseCoordinates rel h (coordinates rel (FreeAbelianGroup.of i)) = _
  rw [coordinates_of]
  change (liftInvariant (Relations rel) (identityExponents rel h)
    (identityExponents_conjugation rel h)
      (toCoinvariants (Relations rel) ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩)).toAdd = _
  rw [liftInvariant_toCoinvariants, identityExponents_relator]
  rfl

/-- Identity-sequence balance implies that the canonical relator coordinates are a basis. -/
theorem coordinates_bijective_of_identity_sequences (h : IdentitySequencesBalanced rel) :
    Function.Bijective (coordinates rel) := by
  refine ⟨?_, coordinates_surjective rel⟩
  apply Function.LeftInverse.injective (g := identityInverseCoordinates rel h)
  intro x
  exact DFunLike.congr_fun (identityInverseCoordinates_comp rel h) x

end SmallPresentationStatements.RelationCoordinates
