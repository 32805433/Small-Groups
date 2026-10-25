module

public import SmallPresentation.SmallCancellationGeometryRelativeFaces
public import SmallPresentation.SmallCancellationGeometryBigonBlocks
public import SmallPresentation.SmallCancellationGeometryBigonConnectivity

/-!
# Region coefficients are the actual last coefficients of suppressed word blocks

The corner transport used for face equations agrees with the last entry of the complete
concatenated block at every surviving dart. Thus the preserved vertex words and preserved
region equations use the same data, rather than independently assigned corner labels.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D Y H : Type*} {P : RibbonMap D} (B : Bigon P)

/-- Reverse a recorded block and reverse each of its original edge ends. -/
def reverseBlock (opposite : Y → Y) (l : List Y) : List Y := l.reverse.map opposite

@[simp] theorem reverseBlock_append (opposite : Y → Y) (u v : List Y) :
    reverseBlock opposite (u ++ v) = reverseBlock opposite v ++ reverseBlock opposite u := by
  simp [reverseBlock]

/-- The exact reversal relation on original incidence tags survives suppression. -/
theorem blocks_reverse (opposite : Y → Y) (block : D → List Y)
    (hblock : ∀ d, block (P.edge d) = reverseBlock opposite (block d)) (d : B.Dart) :
    B.blocks block (B.edge d) = reverseBlock opposite (B.blocks block d) := by
  classical
  by_cases hl : d.val = B.left
  · have hd : d = B.leftDart := Subtype.ext hl
    rw [hd, B.edge_leftDart, B.blocks_eq, B.blocks_eq]
    simp only [leftDart, rightDart, B.left_ne_right, B.left_ne_right.symm, ite_true,
      ite_false, reverseBlock_append, ← hblock, P.edge_involutive B.right]
  by_cases hr : d.val = B.right
  · have hd : d = B.rightDart := Subtype.ext hr
    rw [hd, B.edge_rightDart, B.blocks_eq, B.blocks_eq]
    simp only [leftDart, rightDart, B.left_ne_right, B.left_ne_right.symm, ite_true,
      ite_false, reverseBlock_append, ← hblock, P.edge_involutive B.left]
  have he : (B.edge d).val = P.edge d.val := by
    apply P.bridge_edge_unchanged (P.edge B.left) B.right d.val d.property.1 hr
    · exact P.edge.injective.ne hl
    · intro h
      exact d.property.2 ((P.edge_involutive d.val).symm.trans (congrArg P.edge h))
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

/-- Entrywise relabelling commutes with the actual block concatenations. -/
theorem blocks_map {Z : Type*} (f : Y → Z) (block : D → List Y) (d : B.Dart) :
    (B.blocks block d).map f = B.blocks (fun e ↦ (block e).map f) d := by
  classical
  rw [B.blocks_eq, B.blocks_eq]
  split_ifs <;> simp only [List.map_append]

/-- The first incidence of every nonempty block survives at its retained dart. -/
theorem blocks_head? (block : D → List Y) (hn : ∀ d, block d ≠ []) (d : B.Dart) :
    (B.blocks block d).head? = (block d.val).head? := by
  classical
  have ha (l : List Y) : (block d.val ++ l).head? = (block d.val).head? := by
    cases h : block d.val with
    | nil => exact False.elim (hn d.val h)
    | cons y ys => rfl
  rw [B.blocks_eq]
  split_ifs <;> first | exact ha _ | rfl

/-- The last incidence of a suppressed block is exactly its transported face coordinate. -/
theorem blocks_getLast? (block : D → List Y) (hn : ∀ d, block d ≠ []) (d : B.Dart) :
    (B.blocks block d).getLast? = (block (B.faceCoordinate d)).getLast? := by
  classical
  rw [B.blocks_eq]
  by_cases hl : d.val = B.left
  · rw [ite_eq_left hl]
    change (block d.val ++ block (P.edge B.right)).getLast? =
      (block (B.exchange d.val)).getLast?
    rw [List.getLast?_append_of_ne_nil _ (hn _), hl, B.exchange_left]
  · rw [ite_eq_right hl]
    by_cases hr : d.val = B.right
    · rw [ite_eq_left hr]
      change (block d.val ++ block (P.edge B.left)).getLast? =
        (block (B.exchange d.val)).getLast?
      rw [List.getLast?_append_of_ne_nil _ (hn _), hr, B.exchange_right]
    · rw [ite_eq_right hr]
      change (block d.val).getLast? = (block (B.exchange d.val)).getLast?
      rw [B.exchange_other d hl hr]

/-- Extract the terminal coefficient of a block, using one only for an empty block. -/
def terminalCorner [One H] (coefficient : Y → H) (block : D → List Y) (d : D) : H :=
  (block d).getLast?.elim 1 coefficient

/-- The terminal coefficients of the actual new blocks are the transported old corners. -/
theorem blocks_terminalCorner [One H] (coefficient : Y → H) (block : D → List Y)
    (hn : ∀ d, block d ≠ []) (d : B.Dart) :
    terminalCorner coefficient (B.blocks block) d =
      B.corners (terminalCorner coefficient block) d := by
  change (B.blocks block d).getLast?.elim 1 coefficient =
    (block (B.faceCoordinate d)).getLast?.elim 1 coefficient
  rw [B.blocks_getLast? block hn]

/-- Region products of inverse terminal coefficients from the actual concatenated blocks
are unchanged. -/
theorem block_face_product [Finite D] [Group H] (coefficient : Y → H)
    (block : D → List Y) (hn : ∀ d, block d ≠ []) (d : B.Dart) :
    ((B.suppress.faceBoundary d).map (fun e ↦ (terminalCorner coefficient (B.blocks block) e)⁻¹)).prod =
      ((P.faceBoundary (B.faceCoordinate d)).map (fun e ↦ (terminalCorner coefficient block e)⁻¹)).prod := by
  rw [funext (B.blocks_terminalCorner coefficient block hn)]
  exact B.face_product (fun e ↦ (terminalCorner coefficient block e)⁻¹) d

/-- Every inner-region equation remains valid for the actual block coefficients. -/
theorem inner_block_equations [Finite D] [Group H] (coefficient : Y → H)
    (block : D → List Y) (hn : ∀ d, block d ≠ []) (o : B.FaceDart)
    (h : ∀ d, ¬ P.face.SameCycle o.val d →
      ((P.faceBoundary d).map (fun e ↦ (terminalCorner coefficient block e)⁻¹)).prod = 1)
    (d : B.Dart) (hi : ¬ B.suppress.face.SameCycle (B.outside o) d) :
    ((B.suppress.faceBoundary d).map (fun e ↦ (terminalCorner coefficient (B.blocks block) e)⁻¹)).prod = 1 := by
  rw [funext (B.blocks_terminalCorner coefficient block hn)]
  exact B.inner_equations (fun e ↦ (terminalCorner coefficient block e)⁻¹) o h d hi

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
