module

public import SmallPresentation.SmallCancellationDipoleTopology
public import SmallPresentation.SmallCancellationDipoleRelativePotentials

/-!
# Relative coefficients and quotient paths on actual full-row deletion

The coefficient-free topological deletion is equipped with the original retained corner
labels. Equal quotient potentials on paired removed incidences imply the actual first-return
edge equations. No factor embedding or region equation is used in this construction.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RowRibbon.Dipole

variable {O X H Q : Type} [Finite O] [Group H] [Group Q]
    {words : O → List (SignedLetter X)} {P : RowRibbon words}
    (D : P.Dipole) (L : RibbonLabelling P.map X H)
    (harc : ∀ d, L.arc d = rowRead words d)

/-- The natural inclusion of all incidences belonging to undeleted occurrences. -/
def inclusion (d : RowDarts D.RemainingWords) : RowDarts words := ⟨d.1.val, d.2⟩

/-- Retain the precise original coefficients and arcs on every remaining row. -/
noncomputable def deleteLabelling : RibbonLabelling D.delete.map X H where
  arc d := L.arc (D.inclusion d)
  corner d := L.corner (D.inclusion d)
  edge_arc d := by
    rw [harc, harc]
    exact D.deletedEdge_letters d

variable {q : H →* Q} (F : CornerPotential L q)
    (hpair : ∀ k, F.value ⟨D.second, BasedRowRibbon.inverseCorner D.inverse_words k⟩ =
      F.value ⟨D.first, k⟩)

include hpair in
omit [Finite O] in
/-- The discarded inverse-row matching preserves the original relative quotient potential. -/
theorem corridor_relative_value (d : D.CutDarts) (hd : D.corridor d ≠ d) :
    F.value (D.coordinates (D.corridor d)) = F.value (D.coordinates d) := by
  rcases d with d | (d | d)
  · exact (hd rfl).elim
  · exact hpair d
  · change F.value ⟨D.first, (BasedRowRibbon.inverseCorner D.inverse_words).symm d⟩ =
      F.value ⟨D.second, d⟩
    have hh := hpair ((BasedRowRibbon.inverseCorner D.inverse_words).symm d)
    simpa only [Equiv.apply_symm_apply] using hh.symm

include hpair in
/-- The reconnected retained edge has equal original quotient values at its endpoints. -/
theorem deletedEdge_relative_value (d : RowDarts D.RemainingWords) :
    F.value (D.inclusion (D.deletedEdge d)) = F.value (D.inclusion d) := by
  have hh := D.deletionBands.endpoint_value_of_invariant
    (fun e ↦ F.value (D.coordinates e))
    (fun e ↦ by
      change F.value (D.coordinates (D.cap e)) = _
      rw [D.cap_coordinates]
      exact F.edge _)
    (D.corridor_relative_value L F hpair) (D.retainedEndpoints d)
  have he := D.retainedEndpoints_symm (D.deletionBands.endpoint (D.retainedEndpoints d))
  change F.value (D.coordinates (Sum.inl
    (D.retainedEndpoints.symm (D.deletionBands.endpoint (D.retainedEndpoints d))))) = _
  rw [he]
  exact hh

/-- Full-row deletion carries the exact retained corner potential. -/
noncomputable def deletePotential : CornerPotential (D.deleteLabelling L harc) q where
  value d := F.value (D.inclusion d)
  edge d := D.deletedEdge_relative_value L F hpair d
  rotation d := by
    have hh := F.rotation (D.inclusion d)
    rw [P.rotation_eq] at hh
    exact hh

@[simp] theorem deletePotential_value (d : RowDarts D.RemainingWords) :
    (D.deletePotential L harc F hpair).value d = F.value (D.inclusion d) := rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RowRibbon.Dipole
