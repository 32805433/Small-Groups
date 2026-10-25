module

public import SmallPresentation.SmallCancellationGeometryCornerCancellation
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsFaces
public import SmallPresentation.SmallCancellationGeometryRelativeFaces

/-! Exact face boundaries after splitting and cancelling an adjacent pair. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

open PermutationCycles

variable {D : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

theorem degreeTwo_edge_conjugacy (hn : P.edge C.left ≠ C.right)
    (d : (C.degreeTwo hn).Dart) :
    (C.degreeTwo hn).dartEquiv ((C.degreeTwo hn).suppress.edge d) =
      C.delete.edge ((C.degreeTwo hn).dartEquiv d) := by
  classical
  apply Subtype.ext
  change ((C.degreeTwo hn).dualBigon.bridged.edge d.val) = C.reconnected.edge d.val
  simp only [Bigon.bridged, DegreeTwoVertex.dualBigon, RibbonMap.dual_edge,
    RibbonMap.bridge_edge, reconnected, degreeTwo, split_edge]
  simp only [P.edge_involutive C.left]

theorem degreeTwo_rotation_conjugacy (hn : P.edge C.left ≠ C.right)
    (d : (C.degreeTwo hn).Dart) :
    (C.degreeTwo hn).dartEquiv ((C.degreeTwo hn).suppress.rotation d) =
      C.delete.rotation ((C.degreeTwo hn).dartEquiv d) := by
  apply Subtype.ext
  exact (C.degreeTwo hn).rotation_val d

theorem degreeTwo_face_conjugacy (hn : P.edge C.left ≠ C.right)
    (d : (C.degreeTwo hn).Dart) :
    (C.degreeTwo hn).dartEquiv ((C.degreeTwo hn).suppress.face d) =
      C.delete.face ((C.degreeTwo hn).dartEquiv d) :=
  (C.degreeTwo hn).suppress.relabel_face C.delete (C.degreeTwo hn).dartEquiv
    (C.degreeTwo_edge_conjugacy hn) (C.degreeTwo_rotation_conjugacy hn) d

open Classical in
theorem faceBoundary_filter_of_nonloop [Finite D] (hn : P.edge C.left ≠ C.right) (d : C.Dart) :
    (C.delete.faceBoundary d).map Subtype.val =
      (C.split.faceBoundary d.val).filter (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
  classical
  let A := C.degreeTwo hn
  let e : A.Dart ≃ C.Dart := A.dartEquiv
  have hm := cycleBoundary_map_injective A.suppress.face C.delete.face e e.injective
    (C.degreeTwo_face_conjugacy hn) (e.symm d)
  rw [e.apply_symm_apply d] at hm
  change (A.suppress.faceBoundary (e.symm d)).map e = C.delete.faceBoundary d at hm
  rw [← hm, List.map_map]
  exact A.faceBoundary_filter (e.symm d)

theorem face_step_of_loop (hn : P.edge C.left = C.right) (d : C.Dart) :
    (C.delete.face d).val = C.split.face d.val := by
  have h := congrArg (fun Q : RibbonMap D ↦ Q.face d.val) (C.reconnected_eq_of_loop hn)
  exact h

/-- In the isolated-loop case, retained face walks are entirely unchanged. -/
theorem faceBoundary_of_loop [Finite D] (hn : P.edge C.left = C.right) (d : C.Dart) :
    (C.delete.faceBoundary d).map Subtype.val = C.split.faceBoundary d.val :=
  cycleBoundary_map_injective C.delete.face C.split.face Subtype.val Subtype.val_injective
    (C.face_step_of_loop hn) d

open Classical in
/-- The actual retained faces are exactly the preliminary split faces with the cancelled
pair filtered out. This includes the isolated-loop and two-corner-vertex degeneracies. -/
theorem faceBoundary_filter [Finite D] (d : C.Dart) :
    (C.delete.faceBoundary d).map Subtype.val =
      (C.split.faceBoundary d.val).filter (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
  classical
  by_cases hn : P.edge C.left = C.right
  · rw [← C.faceBoundary_of_loop hn d]
    apply (List.filter_eq_self.mpr ?_).symm
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact of_decide_eq_true (by simpa using (show decide (e.val ≠ C.left ∧ e.val ≠ C.right) = true
      from decide_eq_true_eq.mpr e.property))
  · exact C.faceBoundary_filter_of_nonloop hn d

/-- Actual surviving face cycles correspond exactly to the preliminary split face cycles. -/
theorem sameFace_iff [Finite D] (d e : C.Dart) :
    C.delete.face.SameCycle d e ↔ C.split.face.SameCycle d.val e.val := by
  classical
  rw [← C.delete.mem_faceBoundary_iff, ← C.split.mem_faceBoundary_iff]
  have hm : e ∈ C.delete.faceBoundary d ↔
      e.val ∈ (C.delete.faceBoundary d).map Subtype.val :=
    (List.mem_map_of_injective Subtype.val_injective).symm
  rw [hm, C.faceBoundary_filter]
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, e.property⟩⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
