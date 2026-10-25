module

public import SmallPresentation.SmallCancellationDipolePlanarBands
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler

/-!
# Full-row dipole deletion preserves spherical Euler characteristic

The actual matched-row cuts form a spherical band ribbon. Suppressing all its moving
corridors and discarding closed bands gives precisely the previously defined deletion,
including its original remaining cyclic row orders and first-return edge pairing.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon.Dipole

variable {O X Q : Type} [Group Q] {words : O → List (SignedLetter X)}
    {q : FreeGroup X →* Q} {P : BasedRowRibbon words q} (D : P.Dipole)

theorem deletionRibbon_corridor (d : D.CutDarts) (hd : D.deletionBands.corridor d ≠ d) :
    D.deletionRibbon.rotation d = D.deletionBands.corridor d := by
  rcases d with d | (d | d)
  · exact (hd rfl).elim
  · rfl
  · rfl

variable [Finite O]

/-- A genuine full-row dipole can be deleted without introducing a positive-genus component. -/
theorem delete_euler (hplanar : P.map.EulerEquality) : D.delete.map.EulerEquality := by
  classical
  let := Fintype.ofFinite D.CutDarts
  have hh := D.deletionBands.endpointRibbon_euler D.deletionRibbon (fun _ ↦ rfl)
    D.deletionRibbon_corridor (D.deletionRibbon_euler hplanar)
  apply (D.delete.map.relabel_euler_iff
    (D.deletionBands.endpointRibbon D.deletionRibbon D.deletionRibbon_corridor)
    D.retainedEndpoints ?_ ?_).mpr hh
  · intro d
    change D.retainedEndpoints (D.retainedEndpoints.symm
      (D.deletionBands.endpointPairing (D.retainedEndpoints d))) = _
    exact D.retainedEndpoints.apply_symm_apply _
  · intro d
    apply Subtype.ext
    rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon.Dipole
