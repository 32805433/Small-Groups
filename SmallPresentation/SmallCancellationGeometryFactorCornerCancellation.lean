module

public import SmallPresentation.SmallCancellationDipoleRelativeFactorFaces
public import SmallPresentation.SmallCancellationGeometryRelativeExtractionSystem

/-! Local factor support survives genuine negative-positive corner cancellation. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling.FactorCorners

variable {D A : Type*} {G : A → Type*} [∀ a, Group (G a)]
    {P : RibbonMap D} {L : RibbonLabelling P A (Monoid.CoprodI G)}
    (F : FactorCorners G L) (C : AdjacentCancellation P)
    (harc : L.arc C.right = reverseLetter (L.arc C.left))
    (hnegative : (L.arc C.left).2 = false)

include F hnegative in
/-- Factor support is retained exactly, including the multiplied coefficient at the
predecessor of the deleted pair. No region equation or quotient embedding is needed. -/
theorem cancel : FactorCorners G (C.labelling L harc) := by
  classical
  have hr : (L.arc C.right).2 = true := by
    have hh := F.alternating C.left
    simpa only [C.next, hnegative, Bool.not_false] using hh
  have tags (d : C.Dart) (hd : P.rotation d.val = C.left) :
      (L.arc C.right).1 = (L.arc d.val).1 := by
    have hp : (L.arc d.val).2 = true := by
      have hh := F.alternating d.val
      rw [hd, hnegative] at hh
      cases hs : (L.arc d.val).2
      · rw [hs] at hh
        contradiction
      · rfl
    have hh := F.positive_tag d.val hp
    rw [hd] at hh
    exact (congrArg Prod.fst harc).trans hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    change (L.arc (C.delete.rotation d).val).2 = !(L.arc d.val).2
    rw [C.rotation_val]
    split
    · rename_i hd
      rw [F.alternating C.right, hr]
      have hh := F.alternating d.val
      rwa [hd, hnegative] at hh
    · exact F.alternating d.val
  · intro d hp
    change (L.arc (C.delete.rotation d).val).1 = (L.arc d.val).1
    rw [C.rotation_val]
    split
    · rename_i hd
      exact (F.positive_tag C.right hr).trans (tags d hd)
    · exact F.positive_tag d.val hp
  · intro d hn
    have hd : P.rotation d.val ≠ C.left := by
      intro hd
      have hh := F.alternating d.val
      change (L.arc d.val).2 = false at hn
      rw [hd, hnegative, hn] at hh
      contradiction
    rw [C.labelling_corner_of_ne L harc d hd]
    exact F.negative_one d.val hn
  · intro d
    change (C.labelling L harc).corner d ∈
      (Monoid.CoprodI.of : G (L.arc d.val).1 →* Monoid.CoprodI G).range
    by_cases hd : P.rotation d.val = C.left
    · rw [C.labelling_corner_of_eq L harc d hd]
      apply Subgroup.mul_mem _ (F.coefficient d.val)
      have hh := F.coefficient C.right
      rwa [tags d hd] at hh
    · rw [C.labelling_corner_of_ne L harc d hd]
      exact F.coefficient d.val

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling.FactorCorners
