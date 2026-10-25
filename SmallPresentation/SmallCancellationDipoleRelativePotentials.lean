module

public import SmallPresentation.SmallCancellationGeometryCornerPotentials
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler

/-!
# Relative quotient potentials survive full band suppression

When actual paired corridor incidences have equal quotient potentials, the first-return
edge pairing does too. The retained rotation and corner coefficients are restrictions of
the originals, so the complete relative corner-potential law survives the actual operation.
This applies in particular to deletion of an inverse-row dipole once its paired corner
equalities have been derived from the original marked quotient bases.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem

variable {D X H Q : Type*} [Finite D] [Group H] [Group Q]
    (B : BandSystem D X) (P : RibbonMap D) (L : RibbonLabelling P X H)
    (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)
    (hread : ∀ d, B.letter d = L.arc d)

/-- The exact original arc and corner labels on the retained first-return ribbon. -/
noncomputable def endpointLabelling : RibbonLabelling (B.endpointRibbon P hrot) X H where
  arc d := L.arc d.val
  corner d := L.corner d.val
  edge_arc d := by
    change L.arc (B.endpoint d).val = reverseLetter (L.arc d.val)
    have hh := B.endpoint_letter d
    simpa only [hread] using hh

variable {q : H →* Q} (F : CornerPotential L q)
    (hcap : ∀ d, B.cap d = P.edge d)
    (hcorridor : ∀ d, B.corridor d ≠ d → F.value (B.corridor d) = F.value d)

include hcap hcorridor in
theorem endpoint_value (d : B.Endpoint) : F.value (B.endpoint d).val = F.value d.val := by
  have hh := B.endpoint_potential (fun _ ↦ (1 : Q)) (fun _ ↦ (inv_one).symm)
    F.value (fun d ↦ by rw [hcap, F.edge, mul_one])
    (fun d hd ↦ by rw [hcorridor d hd, mul_one]) d
  simpa only [mul_one] using hh

/-- Actual band suppression retains the original quotient paths at every surviving incidence. -/
noncomputable def endpointPotential :
    CornerPotential (B.endpointLabelling P L hrot hread) q where
  value d := F.value d.val
  edge d := B.endpoint_value P L F hcap hcorridor d
  rotation d := F.rotation d.val

@[simp] theorem endpointPotential_value (d : B.Endpoint) :
    (B.endpointPotential P L hrot hread F hcap hcorridor).value d = F.value d.val := rfl

/-- Constant path values on cap and corridor steps are constant on actual first-return pairs. -/
theorem endpoint_value_of_invariant (f : D → Q)
    (hcapValue : ∀ d, f (B.cap d) = f d)
    (hcorridorValue : ∀ d, B.corridor d ≠ d → f (B.corridor d) = f d)
    (d : B.Endpoint) : f (B.endpoint d).val = f d.val := by
  have hh := B.endpoint_potential (fun _ ↦ (1 : Q)) (fun _ ↦ inv_one.symm) f
    (fun d ↦ by rw [hcapValue, mul_one])
    (fun d hd ↦ by rw [hcorridorValue d hd, mul_one]) d
  simpa only [mul_one] using hh

/-- Only the retained corners need a rotation-potential equation. Internal paired corners
are suppressed, so no equation for their auxiliary degree-two rotation is required. -/
noncomputable def endpointPotentialOfLocal (q : H →* Q) (f : D → Q)
    (hcapValue : ∀ d, f (B.cap d) = f d)
    (hcorridorValue : ∀ d, B.corridor d ≠ d → f (B.corridor d) = f d)
    (hretained : ∀ d : B.Endpoint, f (P.rotation d.val) = f d.val * q (L.corner d.val)) :
    CornerPotential (B.endpointLabelling P L hrot hread) q where
  value d := f d.val
  edge d := B.endpoint_value_of_invariant f hcapValue hcorridorValue d
  rotation d := hretained d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem
