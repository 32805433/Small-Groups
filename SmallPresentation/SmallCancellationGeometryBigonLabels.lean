module

public import SmallPresentation.SmallCancellationGeometryBigonBlocks
public import SmallPresentation.SmallCancellationGeometryBigonConnectivity
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Inverse word labels on suppressed bands

If opposite original edge ends carry inverse words, the concatenated blocks after bigon
suppression obey the same law. Together with the exact vertex-word theorem this permits
iteration with whole bands, instead of incorrectly treating every new edge as a single letter.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D X : Type*} {P : RibbonMap D} (B : Bigon P)

theorem edge_val_of_ne (d : B.Dart) (hl : d.val ≠ B.left) (hr : d.val ≠ B.right) :
    (B.edge d).val = P.edge d.val := by
  apply P.bridge_edge_unchanged (P.edge B.left) B.right d.val d.property.1 hr
  · exact P.edge.injective.ne hl
  · intro h
    exact d.property.2 ((P.edge_involutive d.val).symm.trans (congrArg P.edge h))

/-- Opposite surviving band words are still exact inverse readings. -/
theorem blocks_edge_inverse (block : D → List (SignedLetter X))
    (hblock : ∀ d, block (P.edge d) = FreeGroup.invRev (block d)) (d : B.Dart) :
    B.blocks block (B.edge d) = FreeGroup.invRev (B.blocks block d) := by
  classical
  by_cases hl : d.val = B.left
  · have hd : d = B.leftDart := Subtype.ext hl
    rw [hd, B.edge_leftDart, B.blocks_eq, B.blocks_eq]
    simp only [leftDart, rightDart, B.left_ne_right, B.left_ne_right.symm, ite_true,
      ite_false, hblock, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  by_cases hr : d.val = B.right
  · have hd : d = B.rightDart := Subtype.ext hr
    rw [hd, B.edge_rightDart, B.blocks_eq, B.blocks_eq]
    simp only [leftDart, rightDart, B.left_ne_right, B.left_ne_right.symm, ite_true,
      ite_false, hblock, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  have he := B.edge_val_of_ne d hl hr
  have hel : (B.edge d).val ≠ B.left := by
    rw [he]
    intro h
    exact d.property.1 ((P.edge_involutive d.val).symm.trans (congrArg P.edge h))
  have her : (B.edge d).val ≠ B.right := by
    rw [he]
    intro h
    exact d.property.2 ((P.edge_involutive d.val).symm.trans (congrArg P.edge h))
  rw [B.blocks_eq, B.blocks_eq]
  simp only [hel, her, hl, hr, ite_false]
  rw [he, hblock]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
