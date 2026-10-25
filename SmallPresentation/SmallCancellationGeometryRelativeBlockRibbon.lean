module

public import SmallPresentation.SmallCancellationGeometryRelativeBlocks
public import SmallPresentation.SmallCancellationGeometryBigonLabels
public import SmallPresentation.SmallCancellationGeometryBigonDetection

/-!
# Relative pictures with actual incidence blocks

The fixed alphabet `Y` can be the original dart type. Consequently a block retains original
occurrence and position information even when several original letters have identical labels.
Bigon suppression simultaneously preserves those vertex readings, inverse arc words, and
the region equations computed from the inverses of the same blocks' terminal coefficients.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

/-- A relative ribbon whose edges retain nonempty lists of original incidences. -/
structure RelativeBlockRibbon {D : Type*} (Y X H I : Type*) [Group H]
    (read : Y → SignedLetter X × H) (relators : I → List Y) where
  map : RibbonMap D
  block : D → List Y
  block_nonempty : ∀ d, block d ≠ []
  edge_word : ∀ d, (block (map.edge d)).map (fun y ↦ (read y).1) =
    FreeGroup.invRev ((block d).map (fun y ↦ (read y).1))
  outside : D
  relator : D → I
  relator_word : ∀ d, (map.vertexBoundary d).flatMap block = relators (relator d)
  inner_equation : ∀ d, ¬ map.face.SameCycle outside d →
    ((map.faceBoundary d).map (fun e ↦ (Bigon.terminalCorner (fun y ↦ (read y).2) block e)⁻¹)).prod = 1

namespace RelativeBlockRibbon

variable {D Y X H I : Type*} [Group H]
variable {read : Y → SignedLetter X × H} {relators : I → List Y}
variable (R : RelativeBlockRibbon (D := D) Y X H I read relators)

/-- The first transverse letter in a recorded block. -/
def firstArc (d : D) : Option (SignedLetter X) := (R.block d).head?.map (fun y ↦ (read y).1)

/-- The last transverse letter in a recorded block. -/
def lastArc (d : D) : Option (SignedLetter X) := (R.block d).getLast?.map (fun y ↦ (read y).1)

/-- The coefficient immediately following the full recorded block. -/
def corner (d : D) : H := Bigon.terminalCorner (fun y ↦ (read y).2) R.block d

/-- Cyclic reduction at junctions of recorded blocks. Internal incidences remain in their
original ordered vertex words; this condition tests the junctions created by compression. -/
def CyclicallyReduced : Prop := ∀ d, R.corner d = 1 →
  R.firstArc (R.map.rotation d) ≠ (R.lastArc d).map reverseLetter

/-- Opposite block endpoints have mutually inverse arc readings. -/
theorem firstArc_edge (d : D) :
    R.firstArc (R.map.edge d) = (R.lastArc d).map reverseLetter := by
  have h := congrArg List.head? (R.edge_word d)
  simpa [firstArc, lastArc, FreeGroup.invRev, reverseLetter, Option.map_map,
    Function.comp_def] using h

/-- The full relative block structure after suppressing an actual inner bigon. -/
noncomputable def suppress [Finite D] (B : Bigon R.map)
    (hi : ¬ R.map.face.SameCycle R.outside B.left) :
    RelativeBlockRibbon (D := B.Dart) Y X H I read relators where
  map := B.suppress
  block := B.blocks R.block
  block_nonempty := B.blocks_nonempty R.block R.block_nonempty
  edge_word d := by
    rw [B.blocks_map, B.blocks_map]
    exact B.blocks_edge_inverse (fun e ↦ (R.block e).map (fun y ↦ (read y).1)) R.edge_word d
  outside := B.outside (B.outsideFaceDart R.outside hi)
  relator d := R.relator d.val
  relator_word d := (B.vertex_word R.block d).trans (R.relator_word d.val)
  inner_equation d hd :=
    B.inner_block_equations (fun y ↦ (read y).2) R.block R.block_nonempty
      (B.outsideFaceDart R.outside hi) R.inner_equation d hd

@[simp] theorem suppress_firstArc [Finite D] (B : Bigon R.map)
    (hi : ¬ R.map.face.SameCycle R.outside B.left) (d : B.Dart) :
    (R.suppress B hi).firstArc d = R.firstArc d.val := by
  change (B.blocks R.block d).head?.map _ = (R.block d.val).head?.map _
  rw [B.blocks_head? R.block R.block_nonempty]

@[simp] theorem suppress_lastArc [Finite D] (B : Bigon R.map)
    (hi : ¬ R.map.face.SameCycle R.outside B.left) (d : B.Dart) :
    (R.suppress B hi).lastArc d = R.lastArc (B.faceCoordinate d) := by
  change (B.blocks R.block d).getLast?.map _ = (R.block (B.faceCoordinate d)).getLast?.map _
  rw [B.blocks_getLast? R.block R.block_nonempty]

@[simp] theorem suppress_corner [Finite D] (B : Bigon R.map)
    (hi : ¬ R.map.face.SameCycle R.outside B.left) (d : B.Dart) :
    (R.suppress B hi).corner d = R.corner (B.faceCoordinate d) :=
  B.blocks_terminalCorner (fun y ↦ (read y).2) R.block R.block_nonempty d

/-- Junction cyclic reduction is preserved by the actual block compression. -/
theorem suppress_cyclicallyReduced [Finite D] (B : Bigon R.map)
    (hi : ¬ R.map.face.SameCycle R.outside B.left) (hred : R.CyclicallyReduced) :
    (R.suppress B hi).CyclicallyReduced := by
  intro d hd
  rw [R.suppress_corner B hi] at hd
  have h := hred (B.faceCoordinate d) hd
  rw [R.suppress_firstArc B hi, R.suppress_lastArc B hi]
  change R.firstArc (B.rotation d).val ≠ (R.lastArc (B.faceCoordinate d)).map reverseLetter
  rw [B.rotation_exchange]
  exact h

/-- Cyclic reduction still rules out an inner monogon after compression to whole bands. -/
theorem inner_face_ne_one (hred : R.CyclicallyReduced) (d : D)
    (hi : ¬ R.map.face.SameCycle R.outside d) : (R.map.faceBoundary d).length ≠ 1 := by
  intro hlen
  have hp : Function.minimalPeriod R.map.face d = 1 := by simpa using hlen
  have hfix : R.map.face d = d := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hp
  have hc : R.corner d = 1 := by
    have h := R.inner_equation d hi
    simpa [corner, RibbonMap.faceBoundary, hp] using h
  have he : R.map.edge d = R.map.rotation d := by
    have h := congrArg R.map.rotation hfix
    simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using h
  apply hred d hc
  rw [← he]
  exact R.firstArc_edge d

/-- After eliminating inner bigons, every actual inner face has at least three incidences. -/
theorem three_le_inner_face_length [Finite D] (hc : R.map.Connected)
    (hred : R.CyclicallyReduced)
    (hbigon : ∀ B : Bigon R.map, R.map.face.SameCycle R.outside B.left)
    (d : D) (hi : ¬ R.map.face.SameCycle R.outside d) :
    3 ≤ (R.map.faceBoundary d).length := by
  have hpos := List.length_pos_iff.mpr (R.map.faceBoundary_nonempty d)
  have hone := R.inner_face_ne_one hred d hi
  have htwo : (R.map.faceBoundary d).length ≠ 2 := by
    intro he
    exact hi (hbigon (R.map.innerBigon hc R.outside d hi he))
  omega

end RelativeBlockRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
