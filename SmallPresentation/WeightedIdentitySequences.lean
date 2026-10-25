module

public import SmallPresentation.IdentitySequences

/-!
# Group-valued coordinates of identities among relations

The exponent vector retains the quotient image of each conjugator. Its vanishing on
identity sequences produces a well-defined homomorphism from the normal closure and
then from its abelianization. The construction is general and does not assume small
cancellation, freeness of the ambient group, or finiteness of the relator family.
-/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.Weighted

variable {F Q I J : Type} [Group F] [Group Q]
    (rel : I → F) (p : F →* Q) (label : I → Option J)

/-- Coordinates retain the quotient conjugator and the selected relator label. -/
abbrev Coordinates := FreeAbelianGroup (Q × J)

/-- Relators without a selected label have weight zero. -/
def generator (q : Q) (i : I) : Coordinates (Q := Q) (J := J) :=
  match label i with
  | none => 0
  | some j => FreeAbelianGroup.of (q, j)

/-- The group-ring coefficient vector of a formal word of conjugated relators. -/
def vector : FreeGroup (F × I) →* Multiplicative (Coordinates (Q := Q) (J := J)) :=
  FreeGroup.lift (fun x ↦ Multiplicative.ofAdd (generator label (p x.1) x.2))

/-- Every evaluated identity has zero selected, quotient-weighted coordinate. -/
def Balanced : Prop := (conjugateEvaluation rel).ker ≤ (vector p label).ker

/-- Translation of the quotient coordinate is the underlying additive group action. -/
def shift (q : Q) : Coordinates (Q := Q) (J := J) →+
    Coordinates (Q := Q) (J := J) :=
  FreeAbelianGroup.map (fun x ↦ (q * x.1, x.2))

@[simp] theorem shift_of (q g : Q) (j : J) :
    shift q (FreeAbelianGroup.of (g, j)) = FreeAbelianGroup.of (q * g, j) := by
  simp [shift, FreeAbelianGroup.map]

@[simp] theorem shift_one : shift (J := J) (1 : Q) = AddMonoidHom.id _ := by
  apply FreeAbelianGroup.lift_ext
  rintro ⟨g, j⟩
  simp

@[simp] theorem shift_mul (q r : Q) :
    (shift (J := J) q).comp (shift r) = shift (q * r) := by
  apply FreeAbelianGroup.lift_ext
  rintro ⟨g, j⟩
  simp [mul_assoc]

@[simp] theorem shift_generator (q g : Q) (i : I) :
    shift q (generator label g i) = generator label (q * g) i := by
  cases h : label i <;> simp [generator, h]

/-- The weighted vector is equivariant under changing every conjugator on the left. -/
theorem vector_shift (f : F) (w : FreeGroup (F × I)) :
    vector p label (conjugatorShift f w) =
      (shift (p f)).toMultiplicative (vector p label w) := by
  have h : (vector p label).comp (conjugatorShift f) =
      (shift (p f)).toMultiplicative.comp (vector p label) := by
    apply FreeGroup.ext_hom
    rintro ⟨g, i⟩
    simp [vector, conjugatorShift, map_mul]
  exact DFunLike.congr_fun h w

/-- Identity vanishing makes the weighted coordinate independent of expression. -/
noncomputable def normalCoordinates (h : Balanced rel p label) :
    Relations rel →* Multiplicative (Coordinates (Q := Q) (J := J)) :=
  (normalEvaluation rel).liftOfSurjective (normalEvaluation_surjective rel)
    ⟨vector p label, fun w hw ↦ h (show w ∈ (conjugateEvaluation rel).ker from
      congrArg Subtype.val hw)⟩

@[simp] theorem normalCoordinates_evaluation (h : Balanced rel p label)
    (w : FreeGroup (F × I)) :
    normalCoordinates rel p label h (normalEvaluation rel w) = vector p label w :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The induced relation coordinate has the quotient conjugation action. -/
theorem normalCoordinates_conjugation (h : Balanced rel p label)
    (f : F) (n : Relations rel) :
    normalCoordinates rel p label h (conjugation (Relations rel) f n) =
      (shift (p f)).toMultiplicative (normalCoordinates rel p label h n) := by
  obtain ⟨w, rfl⟩ := normalEvaluation_surjective rel n
  rw [← evaluation_shift, normalCoordinates_evaluation, normalCoordinates_evaluation,
    vector_shift]

/-- Weighted coordinates factor through the full relation abelianization. -/
noncomputable def abelianCoordinates (h : Balanced rel p label) :
    Abelianization (Relations rel) →* Multiplicative (Coordinates (Q := Q) (J := J)) :=
  Abelianization.lift (normalCoordinates rel p label h)

@[simp] theorem abelianCoordinates_of (h : Balanced rel p label) (n : Relations rel) :
    abelianCoordinates rel p label h (Abelianization.of n) =
      normalCoordinates rel p label h n := rfl

/-- The value on the specified relator, with no conjugator. -/
@[simp] theorem normalCoordinates_relator (h : Balanced rel p label) (i : I) :
    normalCoordinates rel p label h
      ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩ =
      Multiplicative.ofAdd (generator label 1 i) := by
  have hr : (⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩ : Relations rel) =
      normalEvaluation rel (FreeGroup.of (1, i)) := by
    apply Subtype.ext
    simp [normalEvaluation, conjugateEvaluation]
  rw [hr, normalCoordinates_evaluation]
  simp [vector]

/-- The weighted coordinate of an actual conjugated relator. -/
@[simp] theorem normalCoordinates_conjugate_relator (h : Balanced rel p label)
    (f : F) (i : I) :
    normalCoordinates rel p label h
      (conjugation (Relations rel) f
        ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩) =
      Multiplicative.ofAdd (generator label (p f) i) := by
  rw [normalCoordinates_conjugation, normalCoordinates_relator]
  change Multiplicative.ofAdd (shift (p f) (generator label 1 i)) = _
  rw [shift_generator, mul_one]

/-- Forgetting the quotient coordinate recovers ordinary exponent sums. -/
def augmentation : Coordinates (Q := Q) (J := J) →+ FreeAbelianGroup J :=
  FreeAbelianGroup.map Prod.snd

/-- Weighted identity balance is stronger than scalar identity balance. -/
theorem balanced_of_all_labelled
    (h : Balanced rel p (some : I → Option I)) : IdentitySequencesBalanced rel := by
  have heq : augmentation.toMultiplicative.comp (vector p (some : I → Option I)) =
      exponentVector (F := F) (I := I) := by
    apply FreeGroup.ext_hom
    rintro ⟨f, i⟩
    simp [vector, generator, augmentation, exponentVector, FreeAbelianGroup.map]
  intro w hw
  have hh := congrArg augmentation.toMultiplicative (h hw)
  change augmentation.toMultiplicative (vector p some w) =
    augmentation.toMultiplicative 1 at hh
  change exponentVector w = 1
  simpa only [← MonoidHom.comp_apply, heq, map_one] using hh

end SmallPresentationStatements.RelationCoordinates.Weighted
