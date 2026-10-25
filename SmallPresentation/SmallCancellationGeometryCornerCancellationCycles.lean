module

public import SmallPresentation.SmallCancellationGeometryRelativeCornerWords
public import SmallPresentation.SmallCancellationGeometryCornerCancellationCounts
public import SmallPresentation.SmallCancellationGeometryEulerComponent

/-! Exact surviving vertex cycles and connectivity after deleting an adjacent loop. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

open PermutationCycles

variable {D : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

open Classical in
theorem vertexBoundary_filter [Finite D] (d : C.Dart) :
    (C.delete.vertexBoundary d).map Subtype.val =
      (P.vertexBoundary d.val).filter (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
  classical
  obtain ⟨l, hw, hm, _⟩ := C.delete_walk (fun e ↦ [e])
    (cycleBoundary_walk P.rotation d.val) d.property d.property
  have hnd : l.Nodup := by
    apply List.Nodup.of_map
    rw [hm]
    exact (cycleBoundary_nodup P.rotation d.val).filter _
  have hn : l ≠ [] := by
    intro hl
    have hs : d.val ∈ (cycleBoundary P.rotation d.val).filter
        (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
      simp [mem_cycleBoundary_self, d.property]
    rw [← hm, hl] at hs
    exact List.not_mem_nil hs
  have hl := hw.eq_cycleBoundary hn hnd
  rw [hl] at hm
  exact hm

/-- Two surviving corners share a vertex exactly when they did before cancellation. -/
theorem sameVertex_iff [Finite D] (d e : C.Dart) :
    C.delete.rotation.SameCycle d e ↔ P.rotation.SameCycle d.val e.val := by
  classical
  rw [← C.delete.mem_vertexBoundary_iff, ← P.mem_vertexBoundary_iff]
  have hm : e ∈ C.delete.vertexBoundary d ↔
      e.val ∈ (C.delete.vertexBoundary d).map Subtype.val :=
    (List.mem_map_of_injective Subtype.val_injective).symm
  rw [hm, C.vertexBoundary_filter]
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, e.property⟩⟩

/-- The split-off pair contributes exactly one vertex. -/
theorem card_split_vertices [Finite D] :
    Fintype.card C.split.Vertex = Fintype.card C.delete.Vertex + 1 := by
  let := Fintype.ofFinite (Cycles C.split.rotation)
  let := Fintype.ofFinite (Cycles
    (offTwoPerm C.split.rotation C.left C.right C.split_rotation_left C.split_rotation_right))
  exact card_offTwoPerm C.split.rotation C.left C.right C.split_rotation_left C.split_rotation_right

/-- Unless the whole old vertex is the deleted pair, its vertex survives once. -/
theorem card_vertices_of_not_two_cycle [Finite D] (hn : P.rotation C.right ≠ C.left) :
    Fintype.card P.Vertex = Fintype.card C.delete.Vertex := by
  have hs := C.card_split_vertices
  have hc : P.rotation.SameCycle C.left (P.rotation C.right) := by
    have hh : P.rotation.SameCycle C.left (P.rotation (P.rotation C.left)) :=
      Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    simpa only [C.next] using hh
  have hv := P.vertexCut_card_vertices_of_sameCycle C.left (P.rotation C.right) hn.symm hc
  change Fintype.card C.split.Vertex = Fintype.card P.Vertex + 1 at hv
  omega

/-- Removing a consecutive loop leaves the retained incidences connected, if any.
The empty result is connected in the usual vacuous sense. -/
theorem delete_connected_of_loop [Finite D] (hc : P.Connected)
    (he : P.edge C.left = C.right) : C.delete.Connected := by
  classical
  let := Fintype.ofFinite D
  have hp := P.card_components_of_connected hc C.left
  have hs := P.vertexCut_card_components C.left (P.rotation C.right) (hc _ _)
  change Fintype.card C.split.Component = Fintype.card P.Component ∨
    Fintype.card C.split.Component = Fintype.card P.Component + 1 at hs
  let p : D → Prop := fun d ↦ d ≠ C.left ∧ d ≠ C.right
  let Q := C.reconnected.restrict (fun d ↦ ¬p d)
    (fun d ↦ not_congr (C.edge_survives d)) (fun d ↦ not_congr (C.rotation_survives d))
  have hQ : 0 < Fintype.card Q.Component := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Quotient.mk _ ⟨C.left, fun h ↦ h.1 rfl⟩⟩
  have hpart := C.reconnected.partition_card_components p C.edge_survives C.rotation_survives
  change Fintype.card C.reconnected.Component =
    Fintype.card C.delete.Component + Fintype.card Q.Component at hpart
  rw [C.reconnected_eq_of_loop he] at hpart
  have hle : Fintype.card C.delete.Component ≤ 1 := by omega
  have hi : Subsingleton C.delete.Component := Fintype.card_le_one_iff_subsingleton.mp hle
  intro d e
  exact Quotient.exact (hi.elim (C.delete.componentClass d) (C.delete.componentClass e))

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
