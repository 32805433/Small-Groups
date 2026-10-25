module

public import SmallPresentation.SmallCancellationGeometryRelativeBlockRibbon

/-!
# Retaining original opposite dart tags through relative picture reduction

When the incidence alphabet is the original dart type, the reversal map is the original
edge involution. It is preserved on the complete lists of tags, not only on their labels.
Consequently later band extraction can recover actual matched original incidences.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

/-- A relative block picture with its exact original-edge reversal on recorded incidences. -/
structure TaggedRelativeBlockRibbon {D : Type*} (Y X H I : Type*) [Group H]
    (read : Y → SignedLetter X × H) (relators : I → List Y) (opposite : Y → Y)
    extends RelativeBlockRibbon (D := D) Y X H I read relators where
  opposite_involutive : Function.Involutive opposite
  edge_tags : ∀ d, block (map.edge d) = Bigon.reverseBlock opposite (block d)
  internal_equations : ∀ d, (block d).IsChain
    (fun y z ↦ (read y).2 * (read (opposite z)).2 = 1)

namespace TaggedRelativeBlockRibbon

variable {D Y X H I : Type*} [Group H]
variable {read : Y → SignedLetter X × H} {relators : I → List Y} {opposite : Y → Y}
variable (R : TaggedRelativeBlockRibbon (D := D) Y X H I read relators opposite)

theorem opposite_mem_last_of_mem_head_edge (d : D) {y : Y}
    (hy : y ∈ (R.block (R.map.edge d)).head?) : opposite y ∈ (R.block d).getLast? := by
  rw [R.edge_tags] at hy
  simp only [Bigon.reverseBlock, List.head?_map, List.head?_reverse] at hy
  obtain ⟨z, hz, hzy⟩ := Option.mem_map.mp hy
  rw [← hzy, R.opposite_involutive z]
  exact hz

theorem corner_eq_of_mem_last (d : D) {y : Y} (hy : y ∈ (R.block d).getLast?) :
    R.toRelativeBlockRibbon.corner d = (read y).2 := by
  change (R.block d).getLast?.elim 1 (fun y ↦ (read y).2) = (read y).2
  have hh : (R.block d).getLast? = some y := hy
  rw [hh]
  rfl

/-- Joining two old blocks across a deleted relative bigon preserves every internal
coefficient equation, including the newly joined pair of original incidences. -/
theorem concat_internal_equations (d e : D)
    (hc : R.toRelativeBlockRibbon.corner d * R.toRelativeBlockRibbon.corner e = 1) :
    (R.block d ++ R.block (R.map.edge e)).IsChain
      (fun y z ↦ (read y).2 * (read (opposite z)).2 = 1) := by
  apply (R.internal_equations d).append (R.internal_equations (R.map.edge e))
  intro y hy z hz
  have hz' := R.opposite_mem_last_of_mem_head_edge e hz
  rw [← R.corner_eq_of_mem_last d hy, ← R.corner_eq_of_mem_last e hz']
  exact hc

/-- Actual inner-bigon surgery retains complete original incidence tags. -/
noncomputable def suppress [Finite D] (B : Bigon R.map)
    (hi : ¬ R.map.face.SameCycle R.outside B.left) :
    TaggedRelativeBlockRibbon (D := B.Dart) Y X H I read relators opposite where
  toRelativeBlockRibbon := R.toRelativeBlockRibbon.suppress B hi
  opposite_involutive := R.opposite_involutive
  edge_tags := B.blocks_reverse opposite R.block R.edge_tags
  internal_equations d := by
    classical
    have hc : R.toRelativeBlockRibbon.corner B.left *
        R.toRelativeBlockRibbon.corner B.right = 1 :=
      R.map.two_step_corner_equation _ _ _ B.face_left B.face_right (R.inner_equation _ hi)
    change (B.blocks R.block d).IsChain _
    rw [B.blocks_eq]
    by_cases hl : d.val = B.left
    · rw [ite_eq_left hl, hl]
      exact R.concat_internal_equations B.left B.right hc
    · rw [ite_eq_right hl]
      by_cases hr : d.val = B.right
      · rw [ite_eq_left hr, hr]
        exact R.concat_internal_equations B.right B.left ((mul_eq_one_iff_eq_inv.mp hc).symm ▸
          mul_inv_cancel (R.toRelativeBlockRibbon.corner B.right))
      · rw [ite_eq_right hr]
        exact R.internal_equations d.val

end TaggedRelativeBlockRibbon

namespace RibbonLabelling

variable {D X H : Type*} [Group H] {P : RibbonMap D}
variable (L : RibbonLabelling P X H)

/-- Initialize recorded blocks with singleton original darts. Original based boundaries are
the relator readings, so repeated letter labels do not identify distinct positions. -/
def taggedBlocks (outside : D)
    (hregions : ∀ d, ¬ P.face.SameCycle outside d → L.faceValue d = 1) :
    TaggedRelativeBlockRibbon (D := D) D X H D (fun d ↦ (L.arc d, L.corner d))
      P.vertexBoundary P.edge where
  map := P
  block d := [d]
  block_nonempty _ := by simp
  edge_word d := by
    simpa [FreeGroup.invRev, reverseLetter] using congrArg (fun x ↦ [x]) (L.edge_arc d)
  outside := outside
  relator := id
  relator_word d := by simp
  inner_equation d hd := by
    change L.faceValue d = 1
    exact hregions d hd
  edge_tags _ := rfl
  opposite_involutive := P.edge_involutive
  internal_equations _ := by simp

/-- Initial junction reduction is precisely the original single-letter cyclic reduction. -/
theorem taggedBlocks_cyclicallyReduced (outside : D)
    (hregions : ∀ d, ¬ P.face.SameCycle outside d → L.faceValue d = 1)
    (hred : L.CyclicallyReduced) :
    (L.taggedBlocks outside hregions).toRelativeBlockRibbon.CyclicallyReduced := by
  intro d hd
  have hc : L.corner d = 1 := hd
  have h := hred d hc
  simpa [RelativeBlockRibbon.firstArc, RelativeBlockRibbon.lastArc, taggedBlocks] using h

end RibbonLabelling

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
