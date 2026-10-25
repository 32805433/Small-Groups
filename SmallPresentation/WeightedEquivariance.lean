module

public import SmallPresentation.RelativeWeightedSplitting

/-! Equivariance of the canonical relation coordinate maps. -/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.WeightedBasis

variable {F I : Type} [Group F] (rel : I → F)

theorem conjugationMap_conjugateClass (f g : F) (i : I) :
    RelationAbelianization.conjugationMap (Relations rel) f (conjugateClass rel g i) =
      conjugateClass rel (f * g) i := by
  change Additive.ofMul (Abelianization.of
    (conjugation (Relations rel) f (conjugation (Relations rel) g (normalRelator rel i)))) =
      Additive.ofMul (Abelianization.of
        (conjugation (Relations rel) (f * g) (normalRelator rel i)))
  congr 2
  apply Subtype.ext
  simp [conjugation, mul_assoc]

/-- Coordinates intertwine quotient translation and the actual conjugation action. -/
theorem coordinates_shift (q : Quotient rel) (v : Coordinates rel) :
    coordinates rel (Weighted.shift q v) =
      RelationAbelianization.quotientAction (Relations rel) q (coordinates rel v) := by
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (Relations rel) q
  rw [RelationAbelianization.quotientAction_mk]
  have heq : (coordinates rel).comp (Weighted.shift (QuotientGroup.mk' (Relations rel) f)) =
      (RelationAbelianization.conjugationMap (Relations rel) f).comp (coordinates rel) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨q, i⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Relations rel) q
    change coordinates rel (Weighted.shift (QuotientGroup.mk' (Relations rel) f)
      (FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) g, i))) = _
    rw [Weighted.shift_of, ← map_mul, coordinates_of]
    change conjugateClass rel (f * g) i =
      RelationAbelianization.conjugationMap (Relations rel) f
        (coordinates rel (FreeAbelianGroup.of (QuotientGroup.mk' (Relations rel) g, i)))
    rw [coordinates_of, conjugationMap_conjugateClass]
  exact DFunLike.congr_fun heq v

end SmallPresentationStatements.RelationCoordinates.WeightedBasis

namespace SmallPresentationStatements.RelationCoordinates.RelativeWeighted

variable {F O I : Type} [Group F] (old : O → F) (new : I → F)

private theorem includeOld_shift (q : Quotient old new) (v : OldCoordinates old new) :
    includeOld old new (Weighted.shift q v) = Weighted.shift q (includeOld old new v) := by
  have heq : (includeOld old new).comp (Weighted.shift q) =
      (Weighted.shift q).comp (includeOld old new) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨g, o⟩
    simp [includeOld, FreeAbelianGroup.map, Weighted.shift]
  exact DFunLike.congr_fun heq v

private theorem includeNew_shift (q : Quotient old new) (v : NewCoordinates old new) :
    includeNew old new (Weighted.shift q v) = Weighted.shift q (includeNew old new v) := by
  have heq : (includeNew old new).comp (Weighted.shift q) =
      (Weighted.shift q).comp (includeNew old new) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨g, i⟩
    simp [includeNew, FreeAbelianGroup.map, Weighted.shift]
  exact DFunLike.congr_fun heq v

/-- The old relation image is invariant under the quotient action. -/
theorem oldMap_shift (q : Quotient old new) (v : OldCoordinates old new) :
    oldMap old new (Weighted.shift q v) =
      RelationAbelianization.quotientAction (Relations (relations old new)) q
        (oldMap old new v) := by
  change WeightedBasis.coordinates (relations old new)
    (includeOld old new (Weighted.shift q v)) = _
  rw [includeOld_shift, WeightedBasis.coordinates_shift]
  rfl

/-- The free new summand has the regular quotient translation action. -/
theorem newMap_shift (q : Quotient old new) (v : NewCoordinates old new) :
    newMap old new (Weighted.shift q v) =
      RelationAbelianization.quotientAction (Relations (relations old new)) q
        (newMap old new v) := by
  change WeightedBasis.coordinates (relations old new)
    (includeNew old new (Weighted.shift q v)) = _
  rw [includeNew_shift, WeightedBasis.coordinates_shift]
  rfl

variable (h : Weighted.Balanced (relations old new)
  (QuotientGroup.mk' (Relations (relations old new))) newLabel)

/-- The selected projection is equivariant, so the splitting retains the group action. -/
theorem projection_action (q : Quotient old new) (x : Module old new) :
    projection old new h
      (RelationAbelianization.quotientAction (Relations (relations old new)) q x) =
      Weighted.shift q (projection old new h x) := by
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (Relations (relations old new)) q
  rw [RelationAbelianization.quotientAction_mk]
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective
    (commutator (Relations (relations old new))) x.toMul
  change (Weighted.normalCoordinates (relations old new)
    (QuotientGroup.mk' (Relations (relations old new))) newLabel h
      (conjugation (Relations (relations old new)) f n)).toAdd = _
  rw [Weighted.normalCoordinates_conjugation]
  rfl

end SmallPresentationStatements.RelationCoordinates.RelativeWeighted
