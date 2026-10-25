module

public import SmallPresentation.SmallCancellationGeometryBigon

/-! The actual face cycles after bigon suppression. -/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D : Type*} {P : RibbonMap D} (B : Bigon P)

/-- Interchange each retained bigon side with the opposite removed edge end. -/
noncomputable def exchange : Equiv.Perm D := by
  classical
  exact (Equiv.swap B.left (P.edge B.right)).trans
    (Equiv.swap B.right (P.edge B.left))

@[simp] theorem exchange_left : B.exchange B.left = P.edge B.right := by
  classical
  simp [exchange, Equiv.swap_apply_of_ne_of_ne, P.edge_ne B.right, B.mate_ne.symm]

@[simp] theorem exchange_right : B.exchange B.right = P.edge B.left := by
  classical
  simp [exchange, Equiv.swap_apply_of_ne_of_ne, B.left_ne_right.symm,
    (P.edge_ne B.right).symm]

@[simp] theorem exchange_mate_left : B.exchange (P.edge B.left) = B.right := by
  classical
  simp [exchange, Equiv.swap_apply_of_ne_of_ne, P.edge_ne B.left, B.mate_ne]

@[simp] theorem exchange_mate_right : B.exchange (P.edge B.right) = B.left := by
  classical
  simp [exchange, Equiv.swap_apply_of_ne_of_ne, B.left_ne_right, (P.edge_ne B.left).symm]

/-- All other surviving darts keep their old face coordinate. -/
theorem exchange_other (d : B.Dart) (hl : d.val ≠ B.left) (hr : d.val ≠ B.right) :
    B.exchange d.val = d.val := by
  classical
  simp [exchange, Equiv.swap_apply_of_ne_of_ne, hl, hr, d.property.1, d.property.2]

/-- Surviving face coordinates are precisely the old darts outside the removed face. -/
abbrev FaceDart := {d : D // d ≠ B.left ∧ d ≠ B.right}

theorem exchange_survives (d : D) :
    (d ≠ P.edge B.left ∧ d ≠ P.edge B.right) ↔
      (B.exchange d ≠ B.left ∧ B.exchange d ≠ B.right) := by
  have ha : B.exchange d ≠ B.left ↔ d ≠ P.edge B.right := by
    rw [← B.exchange_mate_right, B.exchange.injective.ne_iff]
  have hb : B.exchange d ≠ B.right ↔ d ≠ P.edge B.left := by
    rw [← B.exchange_mate_left, B.exchange.injective.ne_iff]
  rw [ha, hb, and_comm]

/-- The local face-coordinate change is a genuine bijection of all surviving darts. -/
noncomputable def faceDartEquiv : B.Dart ≃ B.FaceDart :=
  B.exchange.subtypeEquiv B.exchange_survives

@[simp] theorem faceDartEquiv_val (d : B.Dart) :
    (B.faceDartEquiv d).val = B.exchange d.val := rfl

/-- The old face permutation preserves the complement of the deleted two-cycle. -/
theorem oldFace_survives (d : D) :
    (P.face d ≠ B.left ∧ P.face d ≠ B.right) ↔ (d ≠ B.left ∧ d ≠ B.right) := by
  have ha : P.face d ≠ B.left ↔ d ≠ B.right := by
    rw [← B.face_right, P.face.injective.ne_iff]
  have hb : P.face d ≠ B.right ↔ d ≠ B.left := by
    rw [← B.face_left, P.face.injective.ne_iff]
  rw [ha, hb, and_comm]

/-- The old face permutation restricted to all other faces. -/
noncomputable def oldFace : Equiv.Perm B.FaceDart := P.face.subtypePerm B.oldFace_survives

/-- New vertex succession agrees with old succession after the local face-coordinate change. -/
theorem rotation_exchange (d : B.Dart) :
    (B.rotation d).val = P.rotation (B.exchange d.val) := by
  classical
  rw [B.rotation_val]
  by_cases hl : d.val = B.left
  · rw [ite_eq_left hl, hl, B.exchange_left]
  · rw [ite_eq_right hl]
    by_cases hr : d.val = B.right
    · rw [ite_eq_left hr, hr, B.exchange_right]
    · rw [ite_eq_right hr, B.exchange_other d hl hr]

/-- The new edge reversal agrees with old reversal after the same face-coordinate change. -/
theorem edge_exchange (d : B.Dart) : (B.edge d).val = P.edge (B.exchange d.val) := by
  classical
  rw [B.edge_val]
  by_cases hl : d.val = B.left
  · rw [hl, B.bridged_edge_left, B.exchange_left, P.edge_involutive]
  · by_cases hr : d.val = B.right
    · rw [hr, B.bridged_edge_right, B.exchange_right, P.edge_involutive]
    · rw [B.exchange_other d hl hr]
      change (P.bridge (P.edge B.left) B.right).edge d.val = P.edge d.val
      apply P.bridge_edge_unchanged
      · exact d.property.1
      · exact hr
      · intro h
        have hh := congrArg P.edge h
        rw [P.edge_involutive, P.edge_involutive] at hh
        exact hl hh
      · intro h
        have hh := congrArg P.edge h
        rw [P.edge_involutive] at hh
        exact d.property.2 hh

/-- The actual new face steps are conjugate to the old face steps outside the removed bigon. -/
theorem face_conjugacy (d : B.Dart) :
    B.faceDartEquiv (B.suppress.face d) = B.oldFace (B.faceDartEquiv d) := by
  apply Subtype.ext
  change B.exchange (B.suppress.face d).val = P.face (B.exchange d.val)
  apply P.rotation.injective
  conv_rhs => rw [RibbonMap.face_apply, Equiv.apply_symm_apply]
  rw [← B.rotation_exchange (B.suppress.face d)]
  have h : B.rotation (B.suppress.face d) = B.edge d := by
    change B.rotation (B.rotation.symm (B.edge d)) = B.edge d
    exact B.rotation.apply_symm_apply _
  rw [h, B.edge_exchange]

/-- Exact face cycles after suppression, identified with the old complement of the bigon. -/
noncomputable def facesEquiv [Finite D] :
    B.suppress.Face ≃ PermutationCycles.Cycles B.oldFace :=
  PermutationCycles.conjugateEquiv _ _ B.faceDartEquiv B.face_conjugacy

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
