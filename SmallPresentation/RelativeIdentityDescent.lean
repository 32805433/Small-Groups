module

public import SmallPresentation.RelativeWeightedSplitting

/-! Descent of weighted old/new identities through a quotient by the old relators. -/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.RelativeIdentity

variable {E F Q O I : Type} [Group E] [Group F] [Group Q]
    (old : O → E) (new : I → E)

abbrev allRelations := Sum.elim old new

/-- Tag an old-relator word as a word in all the relators. -/
def oldWord : FreeGroup (E × O) →* FreeGroup (E × (O ⊕ I)) :=
  FreeGroup.map (fun x ↦ (x.1, Sum.inl x.2))

theorem evaluation_oldWord :
    (conjugateEvaluation (allRelations old new)).comp (oldWord (I := I)) =
      conjugateEvaluation old := by
  apply FreeGroup.ext_hom
  rintro ⟨e, o⟩
  simp [oldWord, conjugateEvaluation, allRelations]

/-- Old conjugates carry no selected new coordinate. -/
theorem vector_oldWord (q : E →* Q) :
    (Weighted.vector q (RelativeWeighted.newLabel (O := O) (I := I))).comp
      (oldWord (I := I)) = 1 := by
  apply FreeGroup.ext_hom
  rintro ⟨e, o⟩
  simp [oldWord, Weighted.vector, Weighted.generator, RelativeWeighted.newLabel]

/-- The weighted map vanishes on every old relation, not only the listed generators. -/
theorem normalCoordinates_eq_one_of_old
    (q : E →* Q)
    (h : Weighted.Balanced (allRelations old new) q RelativeWeighted.newLabel)
    (v : Relations (allRelations old new)) (hv : v.val ∈ Relations old) :
    Weighted.normalCoordinates (allRelations old new) q RelativeWeighted.newLabel h v = 1 := by
  obtain ⟨w, hw⟩ := normalEvaluation_surjective old (⟨v.val, hv⟩ : Relations old)
  have heq : normalEvaluation (allRelations old new) (oldWord w) = v := by
    apply Subtype.ext
    change conjugateEvaluation (allRelations old new) (oldWord w) = v.val
    rw [← MonoidHom.comp_apply, evaluation_oldWord]
    exact congrArg Subtype.val hw
  rw [← heq, Weighted.normalCoordinates_evaluation]
  exact DFunLike.congr_fun (vector_oldWord (O := O) (I := I) q) w

variable (p : E →* F) (hp : Function.Surjective p)

/-- Lift only the conjugators; the attaching relator lifts are already fixed. -/
noncomputable def liftWord : FreeGroup (F × I) →* FreeGroup (E × (O ⊕ I)) :=
  FreeGroup.map (fun x ↦ (Classical.choose (hp x.1), Sum.inr x.2))

theorem evaluation_liftWord :
    p.comp ((conjugateEvaluation (allRelations old new)).comp (liftWord (O := O) p hp)) =
      conjugateEvaluation (fun i ↦ p (new i)) := by
  apply FreeGroup.ext_hom
  rintro ⟨f, i⟩
  simp [liftWord, conjugateEvaluation, allRelations, Classical.choose_spec (hp f)]

/-- Forgetting quotient conjugators after lifting gives precisely the original exponent vector. -/
theorem augmentation_liftWord (q : E →* Q) :
    Weighted.augmentation.toMultiplicative.comp
      ((Weighted.vector q RelativeWeighted.newLabel).comp (liftWord (O := O) p hp)) =
      exponentVector (F := F) (I := I) := by
  apply FreeGroup.ext_hom
  rintro ⟨f, i⟩
  simp [liftWord, Weighted.vector, Weighted.generator, RelativeWeighted.newLabel,
    Weighted.augmentation, FreeAbelianGroup.map, exponentVector]

/-- Lifting conjugators retains their quotient coordinate, before augmentation. -/
theorem vector_liftWord (q : F →* Q) :
    (Weighted.vector (q.comp p) RelativeWeighted.newLabel).comp
      (liftWord (O := O) p hp) = Weighted.vector q (some : I → Option I) := by
  apply FreeGroup.ext_hom
  rintro ⟨f, i⟩
  simp [liftWord, Weighted.vector, Weighted.generator, RelativeWeighted.newLabel,
    Classical.choose_spec (hp f)]

include hp in
/-- The stronger group-ring identity statement descends as well: imposing the old
relations does not discard the quotient image of the conjugators. -/
theorem weighted_balanced_descends (hker : p.ker = Relations old) (q : F →* Q)
    (h : Weighted.Balanced (allRelations old new) (q.comp p)
      RelativeWeighted.newLabel) :
    Weighted.Balanced (fun i ↦ p (new i)) q (some : I → Option I) := by
  intro w hw
  let v := normalEvaluation (allRelations old new) (liftWord (O := O) p hp w)
  have hv : v.val ∈ Relations old := by
    rw [← hker]
    change p (conjugateEvaluation (allRelations old new) (liftWord (O := O) p hp w)) = 1
    exact (DFunLike.congr_fun (evaluation_liftWord old new p hp) w).trans hw
  have hz := normalCoordinates_eq_one_of_old old new (q.comp p) h v hv
  change Weighted.normalCoordinates (allRelations old new) (q.comp p)
    RelativeWeighted.newLabel h
    (normalEvaluation (allRelations old new) (liftWord (O := O) p hp w)) = 1 at hz
  rw [Weighted.normalCoordinates_evaluation] at hz
  change Weighted.vector q some w = 1
  exact (DFunLike.congr_fun (vector_liftWord (O := O) p hp q) w).symm.trans hz

include hp in
/-- Weighted identities in a lifted presentation imply balanced identities after imposing
its old relations. This supplies the free-product scalar input from ordinary pictures. -/
theorem balanced_descends (hker : p.ker = Relations old) (q : E →* Q)
    (h : Weighted.Balanced (allRelations old new) q RelativeWeighted.newLabel) :
    IdentitySequencesBalanced (fun i ↦ p (new i)) := by
  intro w hw
  let v := normalEvaluation (allRelations old new) (liftWord (O := O) p hp w)
  have hv : v.val ∈ Relations old := by
    rw [← hker]
    change p (conjugateEvaluation (allRelations old new) (liftWord (O := O) p hp w)) = 1
    have he := DFunLike.congr_fun (evaluation_liftWord old new p hp) w
    exact he.trans hw
  have hz := normalCoordinates_eq_one_of_old old new q h v hv
  change Weighted.normalCoordinates (allRelations old new) q RelativeWeighted.newLabel h
    (normalEvaluation (allRelations old new) (liftWord (O := O) p hp w)) = 1 at hz
  rw [Weighted.normalCoordinates_evaluation] at hz
  have hs := congrArg Weighted.augmentation.toMultiplicative hz
  change exponentVector w = 1
  have he := DFunLike.congr_fun (augmentation_liftWord (O := O) p hp q) w
  exact he.symm.trans (hs.trans (map_one _))

end SmallPresentationStatements.RelationCoordinates.RelativeIdentity
