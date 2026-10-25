module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler

/-!
# Actual surgery deleting two consecutive vertex incidences

Split off the adjacent pair, reconnect its opposite edge ends, and discard the
separated pair. The construction includes a vertex consisting of exactly the pair
and the isolated-loop case. The surviving vertex rotation is the literal cyclic
order with both incidences skipped.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

/-- Two distinct consecutive corners at one actual vertex. -/
structure AdjacentCancellation {D : Type*} (P : RibbonMap D) where
  left : D
  right : D
  ne : left ≠ right
  next : P.rotation left = right

namespace AdjacentCancellation

open PermutationCycles

variable {D : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

/-- Split the two corners into their own vertex. For a two-corner vertex this is the identity. -/
noncomputable def split : RibbonMap D := P.vertexCut C.left (P.rotation C.right)

@[simp] theorem split_edge : C.split.edge = P.edge := rfl

theorem split_rotation_left : C.split.rotation C.left = C.right := by
  classical
  change Equiv.swap C.left (P.rotation C.right) (P.rotation C.left) = C.right
  rw [C.next]
  apply Equiv.swap_apply_of_ne_of_ne C.ne.symm
  intro h
  exact C.ne (P.rotation.injective (C.next.trans h))

theorem split_rotation_right : C.split.rotation C.right = C.left := by
  classical
  exact Equiv.swap_apply_right _ _

theorem split_eq_of_two_cycle (h : P.rotation C.right = C.left) : C.split = P := by
  classical
  apply RibbonMap.ext
  · rfl
  · ext d
    change Equiv.swap C.left (P.rotation C.right) (P.rotation d) = P.rotation d
    rw [h, Equiv.swap_self]
    rfl

theorem split_euler [Fintype D] (h : P.EulerEquality) : C.split.EulerEquality := by
  by_cases ht : P.rotation C.right = C.left
  · rw [C.split_eq_of_two_cycle ht]
    exact h
  · apply P.vertexCut_preserves_euler _ _ (fun he ↦ ht he.symm) ?_ h
    have hs : P.rotation.SameCycle C.left (P.rotation (P.rotation C.left)) :=
      Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    simpa only [C.next] using hs

/-- Surviving corners, retaining their original identities. -/
abbrev Dart := {d : D // d ≠ C.left ∧ d ≠ C.right}

/-- After splitting, exchange edge ends to isolate the deleted pair. -/
noncomputable def reconnected : RibbonMap D := C.split.bridge C.left (P.edge C.right)

theorem reconnected_edge_left : C.reconnected.edge C.left = C.right := by
  have h := C.split.bridge_edge_left C.left (P.edge C.right)
    (by change P.edge (P.edge C.right) ≠ C.left
        rw [P.edge_involutive C.right]
        exact C.ne.symm)
  change C.reconnected.edge C.left = P.edge (P.edge C.right) at h
  rw [P.edge_involutive C.right] at h
  exact h

theorem reconnected_edge_right : C.reconnected.edge C.right = C.left := by
  rw [← C.reconnected_edge_left, C.reconnected.edge_involutive]

theorem edge_survives (d : D) :
    (C.reconnected.edge d ≠ C.left ∧ C.reconnected.edge d ≠ C.right) ↔
      (d ≠ C.left ∧ d ≠ C.right) := by
  simpa only [not_or] using not_congr (twoCycle_invariant C.reconnected.edge C.left C.right
    C.reconnected_edge_left C.reconnected_edge_right d)

theorem rotation_survives (d : D) :
    (C.reconnected.rotation d ≠ C.left ∧ C.reconnected.rotation d ≠ C.right) ↔
      (d ≠ C.left ∧ d ≠ C.right) := by
  change (C.split.rotation d ≠ C.left ∧ C.split.rotation d ≠ C.right) ↔ _
  simpa only [not_or] using not_congr (twoCycle_invariant C.split.rotation C.left C.right
    C.split_rotation_left C.split_rotation_right d)

/-- Delete the two corners after reconnecting their incident edge ends. -/
noncomputable def delete : RibbonMap C.Dart :=
  C.reconnected.restrict (fun d ↦ d ≠ C.left ∧ d ≠ C.right)
    C.edge_survives C.rotation_survives

open Classical in
/-- The precise new cyclic order: skip the deleted pair, and change no other successor. -/
theorem rotation_val (d : C.Dart) :
    (C.delete.rotation d).val =
      if P.rotation d.val = C.left then P.rotation C.right else P.rotation d.val := by
  classical
  change Equiv.swap C.left (P.rotation C.right) (P.rotation d.val) = _
  by_cases hl : P.rotation d.val = C.left
  · rw [hl, Equiv.swap_apply_left, ite_eq_left rfl]
  · rw [ite_eq_right hl]
    exact Equiv.swap_apply_of_ne_of_ne hl (P.rotation.injective.ne d.property.2)

open Classical in
/-- The actual new edge involution is the old involution conjugated by the specified end exchange. -/
theorem edge_val (d : C.Dart) :
    (C.delete.edge d).val =
      Equiv.swap C.left (P.edge C.right) (P.edge (Equiv.swap C.left (P.edge C.right) d.val)) := rfl

open Classical in
/-- Explicit edge reconnection on surviving corners, valid also for the isolated-loop case. -/
theorem edge_val_cases (d : C.Dart) :
    (C.delete.edge d).val =
      if d.val = P.edge C.left then P.edge C.right
      else if d.val = P.edge C.right then P.edge C.left else P.edge d.val := by
  classical
  have hn : C.split.edge (P.edge C.right) ≠ C.left := by
    change P.edge (P.edge C.right) ≠ C.left
    rw [P.edge_involutive C.right]
    exact C.ne.symm
  change C.reconnected.edge d.val = _
  by_cases hl : d.val = P.edge C.left
  · rw [ite_eq_left hl, hl]
    exact C.split.bridge_edge_mate_left C.left (P.edge C.right) hn
  · rw [ite_eq_right hl]
    by_cases hr : d.val = P.edge C.right
    · rw [ite_eq_left hr, hr]
      exact C.split.bridge_edge_right C.left (P.edge C.right) hn
    · rw [ite_eq_right hr]
      apply C.split.bridge_edge_unchanged C.left (P.edge C.right) d.val d.property.1 hr
      · intro he
        apply hl
        exact (P.edge_involutive d.val).symm.trans (congrArg P.edge he)
      · exact P.edge.injective.ne d.property.2

open Classical in
/-- Exact predecessor formula after deleting the consecutive pair. -/
theorem rotation_symm_val (d : C.Dart) :
    (C.delete.rotation.symm d).val =
      if d.val = P.rotation C.right then P.rotation.symm C.left else P.rotation.symm d.val := by
  classical
  change P.rotation.symm (Equiv.swap C.left (P.rotation C.right) d.val) = _
  by_cases hr : d.val = P.rotation C.right
  · rw [ite_eq_left hr, hr, Equiv.swap_apply_right]
  · rw [ite_eq_right hr, Equiv.swap_apply_of_ne_of_ne d.property.1 hr]

open Classical in
/-- Face successors use the reconnected edge and the precise predecessor bypass. -/
theorem face_val (d : C.Dart) :
    (C.delete.face d).val =
      if (C.delete.edge d).val = P.rotation C.right then P.rotation.symm C.left
      else P.rotation.symm (C.delete.edge d).val :=
  C.rotation_symm_val (C.delete.edge d)

/-- In the non-loop case, the intermediate pair is a genuine suppressible degree-two vertex. -/
def degreeTwo (h : P.edge C.left ≠ C.right) : DegreeTwoVertex C.split where
  left := C.left
  right := C.right
  ne := C.ne
  rotation_left := C.split_rotation_left
  rotation_right := C.split_rotation_right
  mate_ne_right := h

theorem delete_euler_of_nonloop [Fintype D] (hn : P.edge C.left ≠ C.right)
    (h : P.EulerEquality) : C.delete.EulerEquality := by
  let A := C.degreeTwo hn
  have hE := A.euler_iff.mpr (C.split_euler h)
  apply (A.suppress.relabel_euler_iff C.delete A.dartEquiv ?_ ?_).mp hE
  · intro d
    apply Subtype.ext
    change (A.dualBigon.bridged.edge d.val) = C.reconnected.edge d.val
    simp only [Bigon.bridged, DegreeTwoVertex.dualBigon, RibbonMap.dual_edge,
      RibbonMap.bridge_edge, reconnected, A, degreeTwo, split_edge]
    simp only [P.edge_involutive C.left]
  · intro d
    apply Subtype.ext
    exact A.rotation_val d

/-- When the two corners form one old edge, the exchange is the identity and the split
pair is an entire endpoint-free component. -/
theorem reconnected_eq_of_loop (h : P.edge C.left = C.right) : C.reconnected = C.split := by
  classical
  have hr : P.edge C.right = C.left := by rw [← h, P.edge_involutive]
  apply RibbonMap.ext
  · ext d
    simp only [reconnected, RibbonMap.bridge_edge, hr, Equiv.swap_self, Equiv.refl_apply]
  · rfl

/-- Adjacent cancellation preserves spherical Euler characteristic, including an entire
length-two vertex, an isolated loop, and component splitting by the preliminary cut. -/
theorem delete_euler [Fintype D] (h : P.EulerEquality) : C.delete.EulerEquality := by
  by_cases hn : P.edge C.left = C.right
  · have he : C.reconnected.EulerEquality := by
      rw [C.reconnected_eq_of_loop hn]
      exact C.split_euler h
    exact C.reconnected.restrict_euler _ C.edge_survives C.rotation_survives he
  · exact C.delete_euler_of_nonloop hn h

end AdjacentCancellation
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
