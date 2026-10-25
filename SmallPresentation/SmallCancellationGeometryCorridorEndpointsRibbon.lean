module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsSuppression
public import SmallPresentation.SmallCancellationGeometryCorridorRelabel

/-!
# Ribbon structure on the retained corridor endpoints
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace BandSystem

variable {D X : Type*} (B : BandSystem D X) (P : RibbonMap D)
  (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)

include hrot in
theorem fixed_rotation_iff (d : D) :
    B.corridor (P.rotation d) = P.rotation d ↔ B.corridor d = d := by
  have hm (x : D) (hx : B.corridor x ≠ x) :
      B.corridor (P.rotation x) ≠ P.rotation x := by
    rw [hrot x hx, B.corridor_involutive]
    exact hx.symm
  constructor
  · intro h
    by_contra hn
    exact hm d hn h
  · intro h
    by_contra hn
    have hb : B.corridor (B.corridor (P.rotation d)) ≠ B.corridor (P.rotation d) := by
      rw [B.corridor_involutive]
      exact fun he ↦ hn he.symm
    have hh := hrot (B.corridor (P.rotation d)) hb
    rw [B.corridor_involutive] at hh
    have hd := P.rotation.injective hh
    have he := congrArg B.corridor hd
    rw [B.corridor_involutive, h] at he
    exact hn (hd.trans he.symm)

/-- Rotation on retained incidences, with edges supplied by the actual first-return pairing. -/
noncomputable def endpointRibbon [Finite D] : RibbonMap B.Endpoint where
  edge := B.endpointPairing
  edge_involutive := B.endpoint_involutive
  edge_ne := B.endpoint_ne
  rotation := P.rotation.subtypePerm (B.fixed_rotation_iff P hrot)

end BandSystem

namespace DegreeTwoVertex

variable {D X : Type*} {P : RibbonMap D} (C : DegreeTwoVertex P)
  (B : BandSystem D X) (hcap : ∀ d, B.cap d = P.edge d)
  (hleft : B.corridor C.left = C.right)
  (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)

include hrot in
theorem suppressed_rotation (d : C.Dart)
    (hd : (C.suppressedBands B hcap hleft).corridor d ≠ d) :
    C.suppress.rotation d = (C.suppressedBands B hcap hleft).corridor d := by
  apply Subtype.ext
  rw [C.rotation_val]
  exact hrot d.val (fun he ↦ hd (Subtype.ext he))

/-- Both the induced rotation and actual first-return pairing survive a corridor deletion. -/
theorem endpointRibbon_suppress_euler_iff [Finite D] :
    (Fintype.card (B.endpointRibbon P hrot).Vertex +
        Fintype.card (B.endpointRibbon P hrot).Face =
      Fintype.card (B.endpointRibbon P hrot).Edge +
        2 * Fintype.card (B.endpointRibbon P hrot).Component) ↔
    (Fintype.card ((C.suppressedBands B hcap hleft).endpointRibbon C.suppress
        (C.suppressed_rotation B hcap hleft hrot)).Vertex +
      Fintype.card ((C.suppressedBands B hcap hleft).endpointRibbon C.suppress
        (C.suppressed_rotation B hcap hleft hrot)).Face =
      Fintype.card ((C.suppressedBands B hcap hleft).endpointRibbon C.suppress
        (C.suppressed_rotation B hcap hleft hrot)).Edge +
      2 * Fintype.card ((C.suppressedBands B hcap hleft).endpointRibbon C.suppress
        (C.suppressed_rotation B hcap hleft hrot)).Component) := by
  apply RibbonMap.relabel_euler_iff _ _ (C.endpointsEquiv B hcap hleft)
  · exact C.endpointsEquiv_pairing B hcap hleft
  · intro d
    apply Subtype.ext
    apply Subtype.ext
    change P.rotation d.val =
      (C.suppress.rotation (C.endpointSurvives B hleft d)).val
    exact (C.rotation_val (C.endpointSurvives B hleft d)).symm

end DegreeTwoVertex
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
