module

public import SmallPresentation.SmallCancellationGeometryPairingFacesCounts
public import SmallPresentation.SmallCancellationGeometryComponents

/-! The one-vertex ribbon realized by a boundary matching is actually connected. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing

variable {X : Type*} {w : List (SignedLetter X)} (P : BoundaryPairing w)

theorem connected : P.ribbon.Connected := by
  intro d e
  apply P.ribbon.component_of_vertexCycle
  exact PermutationCycles.finRotate_sameCycle d e

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing
