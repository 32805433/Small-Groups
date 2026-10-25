module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionRegions

/-! Actual old-corner surgery retains a new-containing component with at most one outside face. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

variable {D X H : Type*} [Fintype D] [Group H] {P : RibbonMap D}
    (C : AdjacentCancellation P) (L : RibbonLabelling P X H)
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hleft : L.corner C.left = 1)
    (outside : D) (hregions : ∀ d, ¬P.face.SameCycle outside d → L.faceValue d = 1)

include hregions in
omit [Fintype D] in
theorem old_bad_face (d : D) (hd : L.faceValue d ≠ 1) : P.face.SameCycle outside d := by
  by_contra h
  exact hd (hregions d h)

include hleft hregions in
/-- Unaffected defective final regions must be the one original outside face. -/
theorem unaffected_bad_unique (ht : P.rotation C.right ≠ C.left) (d e : C.Dart)
    (hda : ¬P.face.SameCycle d.val C.predecessor)
    (hdb : ¬P.face.SameCycle d.val C.right)
    (hea : ¬P.face.SameCycle e.val C.predecessor)
    (heb : ¬P.face.SameCycle e.val C.right)
    (hd : (C.labelling L harc).faceValue d ≠ 1)
    (he : (C.labelling L harc).faceValue e ≠ 1) : C.delete.face.SameCycle d e := by
  rw [C.delete_unaffected_face L harc hleft ht d hda hdb] at hd
  rw [C.delete_unaffected_face L harc hleft ht e hea heb] at he
  exact (C.delete_sameFace_iff_of_unaffected d e hda hdb).mpr
    ((old_bad_face L outside hregions d.val hd).symm.trans
      (old_bad_face L outside hregions e.val he))

include hleft hregions in
/-- If the original outside survives on an unaffected face, both affected old faces are valid. -/
theorem affected_valid_of_unaffected_bad (ht : P.rotation C.right ≠ C.left) (d : C.Dart)
    (ha : ¬P.face.SameCycle d.val C.predecessor)
    (hb : ¬P.face.SameCycle d.val C.right)
    (hd : (C.labelling L harc).faceValue d ≠ 1) :
    L.faceValue C.predecessor = 1 ∧ L.faceValue C.right = 1 := by
  rw [C.delete_unaffected_face L harc hleft ht d ha hb] at hd
  have ho := old_bad_face L outside hregions d.val hd
  constructor
  · exact hregions _ (fun h ↦ ha (ho.symm.trans h))
  · exact hregions _ (fun h ↦ hb (ho.symm.trans h))

omit [Fintype D] in
/-- The second split face has trivial product when its only incidence is deleted. -/
theorem splitLabelling_faceValue_right_of_loop (hn : P.edge C.left = C.right) :
    (C.splitLabelling L).faceValue C.right = 1 := by
  have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (C.split_face_right_of_loop hn)
  simp only [RibbonLabelling.faceValue, RibbonMap.faceBoundary, hp]
  simp [C.splitLabelling_corner_right]

include hleft hregions in
/-- The genuine face-splitting branch, including the old-only-side radial argument. -/
theorem extract_regions_of_split
    (T : OldDiscSystem (C.labelling L harc))
    (hc : P.Connected) (hE : P.EulerEquality)
    (ht : P.rotation C.right ≠ C.left) (hn : P.edge C.left ≠ C.right)
    (hf : P.face.SameCycle C.predecessor C.right)
    (n : C.Dart) (hnew : ¬T.old n) :
    ∃ m o, ¬T.old m ∧ C.delete.SameComponent m o ∧
      ∀ d, C.delete.SameComponent m d → ¬C.delete.face.SameCycle o d →
        (C.labelling L harc).faceValue d = 1 := by
  classical
  let a := C.beforeDart ht
  let b := C.mateDart hn
  have unaffected (d : C.Dart) (ha : ¬ C.delete.face.SameCycle a d)
      (hb : ¬C.delete.face.SameCycle b d) :
      ¬P.face.SameCycle d.val C.predecessor ∧ ¬P.face.SameCycle d.val C.right := by
    rcases C.delete_face_classification ht hn d with h | h | h
    · exact h
    · exact (ha h.symm).elim
    · exact (hb h.symm).elim
  apply T.extract_across_split (C.delete_euler hE) a b
    (C.delete_regions_separated ht hn hE hf)
    (C.component_cover_of_split hc ht hn ((C.split_components_iff_same_face ht hE).mpr hf))
    ?_ ?_ n hnew
  · intro d e hda hdb hea heb hd he
    exact C.unaffected_bad_unique L harc hleft outside hregions ht d e
      (unaffected d hda hdb).1 (unaffected d hda hdb).2
      (unaffected e hea heb).1 (unaffected e hea heb).2 hd he
  · rintro ⟨d, hda, hdb, hd⟩
    have hh := C.affected_valid_of_unaffected_bad L harc hleft outside hregions ht d
      (unaffected d hda hdb).1 (unaffected d hda hdb).2 hd
    apply C.delete_split_face_iff L harc hleft ht hf hh.1 a b (.refl _ _)
    have hs : C.split.face.SameCycle (P.edge C.left) C.right := by
      have h := Equiv.Perm.sameCycle_apply_right.mpr
        (show C.split.face.SameCycle (P.edge C.left) (P.edge C.left) from .refl _ _)
      simpa only [C.split_face_mate] using h
    exact hs.symm

include hleft hregions in
/-- The nonsplitting branch has only the inherited outside equation after selecting its
actual affected face representative. -/
theorem extract_regions_of_merge
    (ht : P.rotation C.right ≠ C.left) (hn : P.edge C.left ≠ C.right)
    (hf : ¬P.face.SameCycle C.predecessor C.right) (n : C.Dart) :
    ∃ o, C.delete.SameComponent n o ∧
      ∀ d, C.delete.SameComponent n d → ¬C.delete.face.SameCycle o d →
        (C.labelling L harc).faceValue d = 1 := by
  classical
  let a := C.beforeDart ht
  have hab := C.delete_affected_faces_sameCycle ht hn hf
  have unaffected (d : C.Dart) (ha : ¬ C.delete.face.SameCycle a d) :
      ¬P.face.SameCycle d.val C.predecessor ∧ ¬P.face.SameCycle d.val C.right := by
    rcases C.delete_face_classification ht hn d with h | h | h
    · exact h
    · exact (ha h.symm).elim
    · exact (ha (hab.trans h.symm)).elim
  apply OldDiscSystem.exists_outside_of_one_affected a n
  · intro d e hd he hvd hve
    exact C.unaffected_bad_unique L harc hleft outside hregions ht d e
      (unaffected d hd).1 (unaffected d hd).2
      (unaffected e he).1 (unaffected e he).2 hvd hve
  · rintro ⟨d, hd, hv⟩
    obtain ⟨ha, hb⟩ := C.affected_valid_of_unaffected_bad L harc hleft outside hregions ht d
      (unaffected d hd).1 (unaffected d hd).2 hv
    exact C.delete_merged_face L harc hleft ht hf ha hb a (.refl _ _)

include hleft hregions in
/-- Adjacent loop cancellation has just one affected surviving face; the other is the
trivial singleton removed by the surgery. -/
theorem extract_regions_of_loop
    (ht : P.rotation C.right ≠ C.left) (hn : P.edge C.left = C.right) (n : C.Dart) :
    ∃ o, C.delete.SameComponent n o ∧
      ∀ d, C.delete.SameComponent n d → ¬C.delete.face.SameCycle o d →
        (C.labelling L harc).faceValue d = 1 := by
  classical
  let a := C.beforeDart ht
  have unaffected (d : C.Dart) (ha : ¬ C.delete.face.SameCycle a d) :
      ¬P.face.SameCycle d.val C.predecessor ∧ ¬P.face.SameCycle d.val C.right := by
    rcases C.delete_face_classification_of_loop ht hn d with h | h
    · exact h
    · exact (ha h.symm).elim
  apply OldDiscSystem.exists_outside_of_one_affected a n
  · intro d e hd he hvd hve
    exact C.unaffected_bad_unique L harc hleft outside hregions ht d e
      (unaffected d hd).1 (unaffected d hd).2
      (unaffected e he).1 (unaffected e he).2 hvd hve
  · rintro ⟨d, hd, hv⟩
    obtain ⟨ha, _⟩ := C.affected_valid_of_unaffected_bad L harc hleft outside hregions ht d
      (unaffected d hd).1 (unaffected d hd).2 hv
    rw [C.delete_faceValue L harc hleft a]
    exact (C.splitLabelling_split_face_iff L ht (C.affected_sameFace_of_loop ht hn) ha).mpr
      (C.splitLabelling_faceValue_right_of_loop L hn)

include hleft hregions in
/-- Disappearing entire old vertices retain all surviving face products literally. -/
theorem extract_regions_of_two_cycle
    (ht : P.rotation C.right = C.left)
    (hvertex : ((P.vertexBoundary C.left).map L.corner).prod = 1) (n : C.Dart) :
    ∃ o, C.delete.SameComponent n o ∧
      ∀ d, C.delete.SameComponent n d → ¬C.delete.face.SameCycle o d →
        (C.labelling L harc).faceValue d = 1 := by
  classical
  apply OldDiscSystem.exists_outside_of_unique_bad n
  intro d e _ _ hd he
  rw [C.delete_faceValue_of_two_cycle L harc ht hleft hvertex d] at hd
  rw [C.delete_faceValue_of_two_cycle L harc ht hleft hvertex e] at he
  apply (C.sameFace_iff d e).mpr
  rw [C.split_eq_of_two_cycle ht]
  exact (old_bad_face L outside hregions d.val hd).symm.trans
    (old_bad_face L outside hregions e.val he)

include hleft hregions in
/-- Every actual old-disc cancellation admits a new-containing component with a single
possible exceptional face. This includes disappearing vertices, loops, merges and splits. -/
theorem extract_regions
    (T : OldDiscSystem (C.labelling L harc))
    (hc : P.Connected) (hE : P.EulerEquality)
    (hvertex : ((P.vertexBoundary C.left).map L.corner).prod = 1)
    (n : C.Dart) (hnew : ¬T.old n) :
    ∃ m o, ¬T.old m ∧ C.delete.SameComponent m o ∧
      ∀ d, C.delete.SameComponent m d → ¬C.delete.face.SameCycle o d →
        (C.labelling L harc).faceValue d = 1 := by
  classical
  by_cases ht : P.rotation C.right = C.left
  · obtain ⟨o, ho, hf⟩ := C.extract_regions_of_two_cycle L harc hleft outside hregions ht
      hvertex n
    exact ⟨n, o, hnew, ho, hf⟩
  · by_cases hl : P.edge C.left = C.right
    · obtain ⟨o, ho, hf⟩ := C.extract_regions_of_loop L harc hleft outside hregions ht hl n
      exact ⟨n, o, hnew, ho, hf⟩
    · by_cases hf : P.face.SameCycle C.predecessor C.right
      · exact C.extract_regions_of_split L harc hleft outside hregions T hc hE ht hl hf n hnew
      · obtain ⟨o, ho, hf⟩ := C.extract_regions_of_merge L harc hleft outside hregions ht hl hf n
        exact ⟨n, o, hnew, ho, hf⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
