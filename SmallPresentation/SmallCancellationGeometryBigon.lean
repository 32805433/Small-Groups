module

public import SmallPresentation.SmallCancellationGeometryRibbonCounts
public import SmallPresentation.PermutationCycleDeletion

/-!
# Suppression of a two-corner face in an actual ribbon map

The two boundary edges of the face are required to be distinct. Their other endpoints may
belong to the same vertex, so the construction permits loop edges and repeated vertices.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {D : Type*}

/-- Two distinct edge sides bounding an actual two-corner face. -/
structure Bigon (P : RibbonMap D) where
  left : D
  right : D
  left_ne_right : left ≠ right
  mate_left_ne_right : P.edge left ≠ right
  face_left : P.face left = right
  face_right : P.face right = left

namespace Bigon

variable {P : RibbonMap D} (B : Bigon P)

theorem mate_ne : P.edge B.left ≠ P.edge B.right :=
  P.edge.injective.ne B.left_ne_right

theorem left_ne_mate_right : B.left ≠ P.edge B.right := by
  intro h
  apply B.mate_left_ne_right
  rw [h, P.edge_involutive]

theorem rotation_left : P.rotation B.left = P.edge B.right := by
  have h := congrArg P.rotation B.face_right
  simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using h.symm

theorem rotation_right : P.rotation B.right = P.edge B.left := by
  have h := congrArg P.rotation B.face_left
  simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using h.symm

/-- Surviving darts after removing the two opposite edge ends. -/
abbrev Dart := {d : D // d ≠ P.edge B.left ∧ d ≠ P.edge B.right}

/-- Bridge the two sides of the bigon before discarding the now separate removed edge. -/
noncomputable def bridged : RibbonMap D := P.bridge (P.edge B.left) B.right

@[simp] theorem bridged_edge_mate_left : B.bridged.edge (P.edge B.left) = P.edge B.right := by
  exact P.bridge_edge_left (P.edge B.left) B.right B.mate_ne.symm

@[simp] theorem bridged_edge_mate_right : B.bridged.edge (P.edge B.right) = P.edge B.left := by
  rw [← B.bridged_edge_mate_left]
  exact B.bridged.edge_involutive _

@[simp] theorem bridged_edge_left : B.bridged.edge B.left = B.right := by
  have h := P.bridge_edge_mate_left (P.edge B.left) B.right B.mate_ne.symm
  change B.bridged.edge (P.edge (P.edge B.left)) = B.right at h
  rw [P.edge_involutive] at h
  exact h

@[simp] theorem bridged_edge_right : B.bridged.edge B.right = B.left := by
  rw [← B.bridged_edge_left]
  exact B.bridged.edge_involutive _

/-- The bridged edge permutation preserves exactly the surviving darts. -/
theorem bridged_survives (d : D) :
    (B.bridged.edge d ≠ P.edge B.left ∧ B.bridged.edge d ≠ P.edge B.right) ↔
      (d ≠ P.edge B.left ∧ d ≠ P.edge B.right) := by
  have ha : B.bridged.edge d ≠ P.edge B.left ↔ d ≠ P.edge B.right := by
    rw [← B.bridged_edge_mate_right, B.bridged.edge.injective.ne_iff]
  have hb : B.bridged.edge d ≠ P.edge B.right ↔ d ≠ P.edge B.left := by
    rw [← B.bridged_edge_mate_left, B.bridged.edge.injective.ne_iff]
  rw [ha, hb, and_comm]

/-- The new involution on actual surviving darts. -/
noncomputable def edge : Equiv.Perm B.Dart :=
  B.bridged.edge.subtypePerm B.bridged_survives

@[simp] theorem edge_val (d : B.Dart) : (B.edge d).val = B.bridged.edge d.val := rfl

theorem edge_involutive : Function.Involutive B.edge := by
  intro d
  apply Subtype.ext
  exact B.bridged.edge_involutive d.val

theorem edge_ne (d : B.Dart) : B.edge d ≠ d := by
  intro h
  exact B.bridged.edge_ne d.val (congrArg Subtype.val h)

/-- The first contracted rotation, with the left mate removed. -/
noncomputable def firstRotation : Equiv.Perm {d : D // d ≠ P.edge B.left} :=
  PermutationCycles.contract P.rotation (P.edge B.left)

/-- The other removed dart survives the first contraction. -/
def secondRemoved : {d : D // d ≠ P.edge B.left} := ⟨P.edge B.right, B.mate_ne.symm⟩

/-- Flatten the successive deletions into the actual surviving dart subtype. -/
def dartEquiv : B.Dart ≃ {d : {d : D // d ≠ P.edge B.left} // d ≠ B.secondRemoved} where
  toFun d := ⟨⟨d.val, d.property.1⟩, fun h ↦ d.property.2 (congrArg Subtype.val h)⟩
  invFun d := ⟨d.val.val, d.val.property, fun h ↦ d.property (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The vertex rotation obtained by bypassing the two removed edge ends. -/
noncomputable def rotation : Equiv.Perm B.Dart :=
  B.dartEquiv.trans ((PermutationCycles.contract B.firstRotation B.secondRemoved).trans
    B.dartEquiv.symm)

/-- Suppress the two-corner face while retaining the actual remaining dart incidences. -/
noncomputable def suppress : RibbonMap B.Dart where
  edge := B.edge
  edge_involutive := B.edge_involutive
  edge_ne := B.edge_ne
  rotation := B.rotation

/-- The first deleted dart belongs to a nontrivial vertex cycle. -/
theorem first_not_fixed : P.rotation (P.edge B.left) ≠ P.edge B.left := by
  intro h
  exact B.mate_left_ne_right (P.rotation.injective (h.trans B.rotation_right.symm))

/-- The second deletion also removes a non-fixed dart after the first contraction. -/
theorem second_not_fixed : B.firstRotation B.secondRemoved ≠ B.secondRemoved := by
  intro h
  have hv := congrArg Subtype.val h
  have hne : P.rotation (P.edge B.right) ≠ P.edge B.left := by
    rw [← B.rotation_right]
    exact P.rotation.injective.ne (P.edge_ne B.right)
  change (PermutationCycles.contract P.rotation (P.edge B.left) B.secondRemoved).val =
    P.edge B.right at hv
  rw [PermutationCycles.contract_val_ne P.rotation (P.edge B.left) B.secondRemoved hne] at hv
  have he : P.rotation (P.edge B.right) = P.rotation B.left := hv.trans B.rotation_left.symm
  exact B.left_ne_mate_right (P.rotation.injective he).symm

/-- Suppression leaves the exact vertex-cycle set unchanged, even when both edges are loops. -/
noncomputable def verticesEquiv [Finite D] : B.suppress.Vertex ≃ P.Vertex :=
  (PermutationCycles.conjugateEquiv B.rotation
    (PermutationCycles.contract B.firstRotation B.secondRemoved) B.dartEquiv
    (fun d ↦ by simp [rotation])).trans
      ((PermutationCycles.contractCyclesEquiv B.firstRotation B.secondRemoved
        B.second_not_fixed).trans
        (PermutationCycles.contractCyclesEquiv P.rotation (P.edge B.left) B.first_not_fixed))

open Classical in
/-- Exact first-stage vertex successor: bypass the left mate after the right face dart. -/
theorem firstRotation_val (d : {d : D // d ≠ P.edge B.left}) :
    (B.firstRotation d).val =
      if d.val = B.right then P.rotation (P.edge B.left) else P.rotation d.val := by
  classical
  by_cases h : d.val = B.right
  · rw [ite_eq_left h]
    exact PermutationCycles.contract_val_eq P.rotation (P.edge B.left) d
      (h ▸ B.rotation_right)
  · rw [ite_eq_right h]
    apply PermutationCycles.contract_val_ne
    intro hh
    exact h (P.rotation.injective (hh.trans B.rotation_right.symm))

/-- The second deleted point's first-stage successor is its original successor. -/
theorem firstRotation_second_val :
    (B.firstRotation B.secondRemoved).val = P.rotation (P.edge B.right) := by
  rw [B.firstRotation_val]
  exact ite_eq_right (P.edge_ne B.right)

/-- Among survivors, exactly the left face dart precedes the second removed point. -/
theorem firstRotation_eq_second_iff (d : B.Dart) :
    B.firstRotation (B.dartEquiv d).val = B.secondRemoved ↔ d.val = B.left := by
  classical
  rw [← Subtype.val_inj, B.firstRotation_val]
  change (if d.val = B.right then P.rotation (P.edge B.left) else P.rotation d.val) =
      P.edge B.right ↔ d.val = B.left
  by_cases h : d.val = B.right
  · rw [ite_eq_left h]
    constructor
    · intro he
      exact False.elim (P.edge_ne B.left
        (P.rotation.injective (he.trans B.rotation_left.symm)))
    · intro he
      exact False.elim (B.left_ne_right (he.symm.trans h))
  · rw [ite_eq_right h]
    exact ⟨fun he ↦ P.rotation.injective (he.trans B.rotation_left.symm),
      fun he ↦ (congrArg P.rotation he).trans B.rotation_left⟩

open Classical in
/-- Exact vertex successor after suppression, with the two local bypasses exposed. -/
theorem rotation_val (d : B.Dart) :
    (B.rotation d).val = if d.val = B.left then P.rotation (P.edge B.right)
      else if d.val = B.right then P.rotation (P.edge B.left) else P.rotation d.val := by
  classical
  change (PermutationCycles.contract B.firstRotation B.secondRemoved (B.dartEquiv d)).val.val = _
  by_cases h : d.val = B.left
  · rw [ite_eq_left h]
    rw [PermutationCycles.contract_val_eq B.firstRotation B.secondRemoved (B.dartEquiv d)
      ((B.firstRotation_eq_second_iff d).mpr h), B.firstRotation_second_val]
  · rw [ite_eq_right h]
    rw [PermutationCycles.contract_val_ne B.firstRotation B.secondRemoved (B.dartEquiv d)
      (fun hh ↦ h ((B.firstRotation_eq_second_iff d).mp hh)), B.firstRotation_val]
    rfl

end Bigon

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
