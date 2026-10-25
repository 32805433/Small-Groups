module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionStep

/-! Region validity for nonsplitting corner cancellation and the exact split obstruction. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

variable {D X H : Type*} [Fintype D] [Group H] {P : RibbonMap D}
    (C : AdjacentCancellation P) (L : RibbonLabelling P X H)
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hleft : L.corner C.left = 1)
    (hfaces : ∀ d, L.faceValue d = 1)

include hleft hfaces in
/-- Merging two formerly distinct valid coefficient faces preserves every region equation. -/
theorem all_faces_of_merge (ht : P.rotation C.right ≠ C.left)
    (hf : ¬P.face.SameCycle C.predecessor C.right) (e : C.Dart) :
    (C.labelling L harc).faceValue e = 1 := by
  rcases C.face_classification ht e with h | h | h
  · rw [C.delete_unaffected_face L harc hleft ht e h.1 h.2]
    exact hfaces e.val
  · exact C.delete_merged_face L harc hleft ht hf (hfaces _) (hfaces _) e h.symm
  · apply C.delete_merged_face L harc hleft ht hf (hfaces _) (hfaces _) e
    have hh : C.split.face.SameCycle C.predecessor C.right := by
      rw [C.split_face]
      exact PermutationCycles.cutAt_sameCycle_of_not_sameCycle P.face _ _ hf
    exact hh.trans h.symm

include hleft hfaces in
/-- A cancelled adjacent loop separates only a trivial singleton face; all retained
regions remain valid. -/
theorem all_faces_of_loop (ht : P.rotation C.right ≠ C.left)
    (hl : P.edge C.left = C.right) (e : C.Dart) :
    (C.labelling L harc).faceValue e = 1 := by
  rcases C.delete_face_classification_of_loop ht hl e with h | h
  · rw [C.delete_unaffected_face L harc hleft ht e h.1 h.2]
    exact hfaces e.val
  · have hb : (C.labelling L harc).faceValue (C.beforeDart ht) = 1 := by
      rw [C.delete_faceValue L harc hleft]
      exact (C.splitLabelling_split_face_iff L ht (C.affected_sameFace_of_loop ht hl)
        (hfaces _)).mpr (C.splitLabelling_faceValue_right_of_loop L hl)
    exact ((C.labelling L harc).faceValue_eq_one_of_sameCycle h).mpr hb

include hleft hfaces in
/-- In a genuine face split, all defects are confined to the two displayed new faces. -/
theorem faces_outside_split (ht : P.rotation C.right ≠ C.left)
    (hl : P.edge C.left ≠ C.right) (e : C.Dart)
    (ha : ¬C.delete.face.SameCycle (C.beforeDart ht) e)
    (hb : ¬C.delete.face.SameCycle (C.mateDart hl) e) :
    (C.labelling L harc).faceValue e = 1 := by
  rcases C.delete_face_classification ht hl e with h | h | h
  · rw [C.delete_unaffected_face L harc hleft ht e h.1 h.2]
    exact hfaces e.val
  · exact (ha h.symm).elim
  · exact (hb h.symm).elim

include hleft hfaces in
/-- The two potentially defective faces are trivial simultaneously. This is the
noncommutative cut-product relation, not independent validity of either face. -/
theorem split_faces_equivalent (ht : P.rotation C.right ≠ C.left)
    (hl : P.edge C.left ≠ C.right) (hf : P.face.SameCycle C.predecessor C.right) :
    (C.labelling L harc).faceValue (C.beforeDart ht) = 1 ↔
      (C.labelling L harc).faceValue (C.mateDart hl) = 1 := by
  apply C.delete_split_face_iff L harc hleft ht hf (hfaces _) _ _ (.refl _ _)
  have hh : C.split.face.SameCycle (P.edge C.left) (C.split.face (P.edge C.left)) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  rw [C.split_face_mate] at hh
  exact hh.symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
