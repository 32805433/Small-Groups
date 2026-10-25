module

public import SmallPresentation.SmallCancellationDipoleDeletion
public import SmallPresentation.SmallCancellationDipolePairRefinement
public import SmallPresentation.SmallCancellationGeometryCorridorRelabel

/-!
# The actual dipole bands form a spherical ribbon

Splice the two rows along the specified actual anchor edge and then make the proved
noncrossing cuts into opposite corner pairs. This produces the exact corridor pairing
used by dipole deletion; every other row rotation and every original edge is retained.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon.Dipole

open PermutationCycles

variable {O X Q : Type} [Group Q] {words : O → List (SignedLetter X)}
    {q : FreeGroup X →* Q} {P : BasedRowRibbon words q} (D : P.Dipole)

def originalRotation : Equiv.Perm D.CutDarts :=
  Equiv.sumCongr (rowRotation D.RemainingWords)
    (Equiv.sumCongr (finRotate (words D.first).length) (finRotate (words D.second).length))

def pairedRotation : Equiv.Perm D.CutDarts :=
  Equiv.sumCongr (rowRotation D.RemainingWords) (RowDeletion.interchange (inverseCorner D.inverse_words))

noncomputable def originalRibbon : RibbonMap D.CutDarts where
  edge := D.cap
  edge_involutive := D.cap_involutive
  edge_ne d hd := P.map.edge_ne (D.coordinates d)
    ((D.cap_coordinates d).symm.trans (congrArg D.coordinates hd))
  rotation := D.originalRotation

theorem originalRotation_coordinates (d : D.CutDarts) :
    D.coordinates (D.originalRotation d) = P.map.rotation (D.coordinates d) := by
  rw [P.rotation_eq]
  rcases d with ⟨o, d⟩ | (d | d) <;> rfl

theorem cap_anchor :
    D.cap (.inr (.inl D.anchor)) = .inr (.inr (inverseCorner D.inverse_words D.anchor)) := by
  apply D.coordinates.injective
  rw [D.cap_coordinates]
  exact D.edge_anchor

theorem pair_refinement :
    SplitRefinement
      (cutAt D.originalRotation
        (.inr (.inl (finRotate _ D.anchor)))
        (.inr (.inr (inverseCorner D.inverse_words D.anchor))))
      D.pairedRotation := by
  have hh := cast_anchored_pairing_refinement
    (show (words D.first).length = (words D.second).length from by
      rw [D.inverse_words, FreeGroup.invRev_length]) D.anchor
  have ht := hh.sum_right (rowRotation D.RemainingWords)
  rw [← cutAt_sum_right] at ht
  exact ht

variable [Finite O]

theorem originalRibbon_euler_iff :
    (Fintype.card D.originalRibbon.Vertex + Fintype.card D.originalRibbon.Face =
      Fintype.card D.originalRibbon.Edge + 2 * Fintype.card D.originalRibbon.Component) ↔
    (Fintype.card P.map.Vertex + Fintype.card P.map.Face =
      Fintype.card P.map.Edge + 2 * Fintype.card P.map.Component) :=
  D.originalRibbon.relabel_euler_iff P.map D.coordinates D.cap_coordinates
    D.originalRotation_coordinates

theorem originalRibbon_anchor_distinct :
    ¬D.originalRibbon.rotation.SameCycle (.inr (.inl D.anchor))
      (D.originalRibbon.edge (.inr (.inl D.anchor))) := by
  intro h
  have hh := sameCycle_map_of_step D.originalRibbon.rotation P.map.rotation D.coordinates
    (fun d ↦ by
      change P.map.rotation.SameCycle (D.coordinates d) (D.coordinates (D.originalRotation d))
      rw [D.originalRotation_coordinates]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) h
  change P.map.rotation.SameCycle (D.coordinates (.inr (.inl D.anchor)))
    (D.coordinates (D.cap (.inr (.inl D.anchor)))) at hh
  rw [D.cap_coordinates] at hh
  exact D.anchor_distinct_vertices hh

/-- This is the exact ribbon whose degree-two vertices are the removed matched row corners. -/
noncomputable def deletionRibbon : RibbonMap D.CutDarts :=
  D.originalRibbon.withRotation D.pairedRotation

/-- The actual paired-corner ribbon remains spherical, including all disconnected components. -/
theorem deletionRibbon_euler
    (hplanar : Fintype.card P.map.Vertex + Fintype.card P.map.Face =
      Fintype.card P.map.Edge + 2 * Fintype.card P.map.Component) :
    Fintype.card D.deletionRibbon.Vertex + Fintype.card D.deletionRibbon.Face =
      Fintype.card D.deletionRibbon.Edge + 2 * Fintype.card D.deletionRibbon.Component := by
  classical
  let := Fintype.ofFinite D.CutDarts
  have hs := (D.originalRibbon.edgeSplice_euler_iff (.inr (.inl D.anchor))
    D.originalRibbon_anchor_distinct).mpr (D.originalRibbon_euler_iff.mpr hplanar)
  have href : SplitRefinement
      (D.originalRibbon.edgeSplice (.inr (.inl D.anchor))).rotation D.pairedRotation := by
    change SplitRefinement
      (cutAt D.originalRotation (.inr (.inl (finRotate _ D.anchor)))
        (D.cap (.inr (.inl D.anchor)))) D.pairedRotation
    rw [D.cap_anchor]
    exact D.pair_refinement
  exact (D.originalRibbon.edgeSplice (.inr (.inl D.anchor))).splitRefinement_preserves_euler
    href hs

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon.Dipole
