module

public import SmallPresentation.WeightedRelationBasis

/-!
# Splitting old and new relation classes

Weighted independence of the new relators splits the full relation abelianization
into its old-relator image and a free group-ring coordinate summand. Old relations
are not assumed independent; their image is retained with all its relations.
-/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.RelativeWeighted

variable {F O I : Type} [Group F] (old : O → F) (new : I → F)

abbrev relations := Sum.elim old new
abbrev Quotient := WeightedBasis.Quotient (relations old new)
abbrev Module := WeightedBasis.Module (relations old new)
abbrev OldCoordinates := FreeAbelianGroup (Quotient old new × O)
abbrev NewCoordinates := FreeAbelianGroup (Quotient old new × I)
abbrev AllCoordinates := WeightedBasis.Coordinates (relations old new)

/-- Select precisely the newly attached relators. -/
def newLabel : O ⊕ I → Option I := Sum.elim (fun _ ↦ none) some

/-- Include old labelled conjugates in the coordinates for all relations. -/
def includeOld : OldCoordinates old new →+ AllCoordinates old new :=
  FreeAbelianGroup.map (fun x ↦ (x.1, Sum.inl x.2))

/-- Include new labelled conjugates in the coordinates for all relations. -/
def includeNew : NewCoordinates old new →+ AllCoordinates old new :=
  FreeAbelianGroup.map (fun x ↦ (x.1, Sum.inr x.2))

/-- Old-coordinate projection before evaluating relations. -/
def selectOld : AllCoordinates old new →+ OldCoordinates old new :=
  FreeAbelianGroup.lift (fun x ↦ match x.2 with
    | Sum.inl o => FreeAbelianGroup.of (x.1, o)
    | Sum.inr _ => 0)

/-- New-coordinate projection before evaluating relations. -/
def selectNew : AllCoordinates old new →+ NewCoordinates old new :=
  FreeAbelianGroup.lift (fun x ↦ Weighted.generator newLabel x.1 x.2)

/-- The original coordinate group is the sum of its old and new parts. -/
theorem coordinates_decompose (x : AllCoordinates old new) :
    includeOld old new (selectOld old new x) + includeNew old new (selectNew old new x) = x := by
  have h : (includeOld old new).comp (selectOld old new) +
      (includeNew old new).comp (selectNew old new) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨q, o | i⟩ <;>
      simp [includeOld, includeNew, selectOld, selectNew, newLabel,
        Weighted.generator, FreeAbelianGroup.map]
  exact DFunLike.congr_fun h x

/-- Actual old-relator classes in the full relation abelianization. -/
noncomputable def oldMap : OldCoordinates old new →+ Module old new :=
  (WeightedBasis.coordinates (relations old new)).comp (includeOld old new)

/-- Actual new-relator classes in the full relation abelianization. -/
noncomputable def newMap : NewCoordinates old new →+ Module old new :=
  (WeightedBasis.coordinates (relations old new)).comp (includeNew old new)

variable (h : Weighted.Balanced (relations old new)
  (QuotientGroup.mk' (Relations (relations old new))) newLabel)

/-- The selected coordinate supplied by weighted identity vanishing. -/
noncomputable def projection : Module old new →+ NewCoordinates old new :=
  (Weighted.abelianCoordinates (relations old new)
    (QuotientGroup.mk' (Relations (relations old new))) newLabel h).toAdditive

/-- The projection has the correct value on every actual conjugated relation. -/
theorem projection_coordinates :
    (projection old new h).comp (WeightedBasis.coordinates (relations old new)) =
      selectNew old new := by
  apply FreeAbelianGroup.lift_ext
  rintro ⟨q, r⟩
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (Relations (relations old new)) q
  change projection old new h (WeightedBasis.coordinates (relations old new)
    (FreeAbelianGroup.of (QuotientGroup.mk' (Relations (relations old new)) f, r))) = _
  rw [WeightedBasis.coordinates_of]
  change (Weighted.normalCoordinates (relations old new)
    (QuotientGroup.mk' (Relations (relations old new))) newLabel h
      (conjugation (Relations (relations old new)) f
        (WeightedBasis.normalRelator (relations old new) r))).toAdd = _
  rw [WeightedBasis.normalRelator, Weighted.normalCoordinates_conjugate_relator]
  simp [selectNew]

@[simp] theorem projection_oldMap :
    (projection old new h).comp (oldMap old new) = 0 := by
  rw [oldMap, ← AddMonoidHom.comp_assoc, projection_coordinates]
  apply FreeAbelianGroup.lift_ext
  rintro ⟨q, o⟩
  simp [includeOld, selectNew, FreeAbelianGroup.map, Weighted.generator, newLabel]

@[simp] theorem projection_newMap :
    (projection old new h).comp (newMap old new) = AddMonoidHom.id _ := by
  rw [newMap, ← AddMonoidHom.comp_assoc, projection_coordinates]
  apply FreeAbelianGroup.lift_ext
  rintro ⟨q, i⟩
  simp [includeNew, selectNew, FreeAbelianGroup.map, Weighted.generator, newLabel]

/-- The kernel is exactly the image of old relators; no independence of old relators is assumed. -/
theorem projection_ker : (projection old new h).ker = (oldMap old new).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := WeightedBasis.coordinates_surjective (relations old new) x
    have hv : selectNew old new v = 0 := by
      rw [← DFunLike.congr_fun (projection_coordinates old new h) v]
      exact hx
    refine ⟨selectOld old new v, ?_⟩
    have heq := congrArg (WeightedBasis.coordinates (relations old new))
      (coordinates_decompose old new v)
    simpa only [hv, map_zero, add_zero, oldMap, AddMonoidHom.comp_apply] using heq
  · rintro ⟨v, rfl⟩
    exact DFunLike.congr_fun (projection_oldMap old new h) v

/-- The direct-sum map uses the actual old image and the new conjugate coordinates. -/
noncomputable def splittingMap : (oldMap old new).range × NewCoordinates old new →+
    Module old new := (oldMap old new).range.subtype.coprod (newMap old new)

include h in
/-- Weighted identities produce a canonical split relation sequence. -/
theorem splittingMap_bijective : Function.Bijective (splittingMap old new) := by
  constructor
  · rintro ⟨x, u⟩ ⟨y, v⟩ heq
    have hp := congrArg (projection old new h) heq
    have hx : projection old new h x.val = 0 := by
      have hm : x.val ∈ (projection old new h).ker := by
        rw [projection_ker]
        exact x.property
      exact hm
    have hy : projection old new h y.val = 0 := by
      have hm : y.val ∈ (projection old new h).ker := by
        rw [projection_ker]
        exact y.property
      exact hm
    have hu : projection old new h (newMap old new u) = u :=
      DFunLike.congr_fun (projection_newMap old new h) u
    have hv : projection old new h (newMap old new v) = v :=
      DFunLike.congr_fun (projection_newMap old new h) v
    change projection old new h (x.val + newMap old new u) =
      projection old new h (y.val + newMap old new v) at hp
    rw [map_add, map_add, hx, hy, zero_add, zero_add, hu, hv] at hp
    subst v
    have hxy : x = y := Subtype.ext (add_right_cancel heq)
    subst y
    rfl
  · intro x
    let v := projection old new h x
    have hm : x - newMap old new v ∈ (oldMap old new).range := by
      rw [← projection_ker old new h]
      change projection old new h (x - newMap old new v) = 0
      rw [map_sub]
      have hv := DFunLike.congr_fun (projection_newMap old new h) v
      change projection old new h (newMap old new v) = v at hv
      rw [hv]
      exact sub_self _
    exact ⟨(⟨x - newMap old new v, hm⟩, v), sub_add_cancel _ _⟩

/-- The old image and the free new coordinate summand reconstruct the full relation module. -/
noncomputable def splittingEquiv :
    (oldMap old new).range × NewCoordinates old new ≃+ Module old new :=
  AddEquiv.ofBijective (splittingMap old new) (splittingMap_bijective old new h)

end SmallPresentationStatements.RelationCoordinates.RelativeWeighted
