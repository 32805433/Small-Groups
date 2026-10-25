module

public import SmallPresentation.SmallCancellationGeometryCorridorPlanarity
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler
public import SmallPresentation.SmallCancellationGeometryEulerComponent
public import SmallPresentation.SmallCancellationGeometryIdentityVertices

/-!
# The relator ribbon constructed from an identity is spherical

Starting from the noncrossing free-reduction cap, actual vertex cuts separate the
literal conjugator blocks. Actual corridor suppression then produces precisely the
previously defined first-return edge pairing on the original signed relator rows.
Every nonempty resulting component has sphere Euler characteristic. Empty rows and
closed bands contribute no spurious vertices or components to the retained ribbon.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))

/-- The originally constructed relator ribbon satisfies the sphere equation in total,
with its actual number of components and no auxiliary planarity assumption. -/
theorem relatorRibbon_euler (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    Fintype.card (relatorRibbon paths rows s h).Vertex +
        Fintype.card (relatorRibbon paths rows s h).Face =
      Fintype.card (relatorRibbon paths rows s h).Edge +
        2 * Fintype.card (relatorRibbon paths rows s h).Component := by
  let B := bands paths rows s h
  let P := corridorRibbon paths rows s h
  have hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d :=
    corridorRotation_off_disc paths rows s
  have hE := B.endpointRibbon_euler P (fun _ ↦ rfl) hrot (corridorRibbon_euler paths rows s h)
  apply ((relatorRibbon paths rows s h).relabel_euler_iff (B.endpointRibbon P hrot)
    (discEndpointEquiv paths rows s h) ?_ ?_).mpr hE
  · intro d
    change (discEndpointEquiv paths rows s h)
      ((discEndpointEquiv paths rows s h).symm
        (B.endpointPairing (discEndpointEquiv paths rows s h d))) = _
    exact (discEndpointEquiv paths rows s h).apply_symm_apply _
  · intro d
    apply Subtype.ext
    exact (corridorRotation_disc paths rows s d).symm

/-- Each actual nonempty component of the relator ribbon is a sphere in Euler characteristic. -/
theorem relatorRibbon_component_sphere (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)
    (d : DiscDarts rows s) :
    Fintype.card ((relatorRibbon paths rows s h).componentRibbon d).Vertex +
        Fintype.card ((relatorRibbon paths rows s h).componentRibbon d).Face =
      Fintype.card ((relatorRibbon paths rows s h).componentRibbon d).Edge + 2 :=
  (relatorRibbon paths rows s h).componentRibbon_sphere (relatorRibbon_euler paths rows s h) d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
