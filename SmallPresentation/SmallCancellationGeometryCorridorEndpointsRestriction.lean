module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsRibbon
public import SmallPresentation.SmallCancellationGeometryEulerRestriction

/-! Removing endpoint-free invariant components preserves the induced endpoint ribbon. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem

open PermutationCycles

variable {D X : Type*} (B : BandSystem D X) (p : D → Prop)
  (hc : ∀ d, p (B.cap d) ↔ p d) (hb : ∀ d, p (B.corridor d) ↔ p d)

noncomputable def restricted : BandSystem {d : D // p d} X where
  cap := B.cap.subtypePerm hc
  corridor := B.corridor.subtypePerm hb
  cap_involutive d := Subtype.ext (B.cap_involutive d.val)
  corridor_involutive d := Subtype.ext (B.corridor_involutive d.val)
  letter d := B.letter d.val
  cap_letter d := B.cap_letter d.val
  corridor_letter d hd := B.corridor_letter d.val (fun he ↦ hd (Subtype.ext he))

variable (hp : ∀ d : B.Endpoint, p d.val)

def restrictedEndpointsEquiv : B.Endpoint ≃ (B.restricted p hc hb).Endpoint where
  toFun d := ⟨⟨d.val, hp d⟩, Subtype.ext d.property⟩
  invFun d := ⟨d.val.val, congrArg Subtype.val d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem restrictedEndpointsEquiv_pairing [Finite D] (d : B.Endpoint) :
    B.restrictedEndpointsEquiv p hc hb hp (B.endpointPairing d) =
      (B.restricted p hc hb).endpointPairing (B.restrictedEndpointsEquiv p hc hb hp d) := by
  let B' := B.restricted p hc hb
  let e := B.restrictedEndpointsEquiv p hc hb hp
  let d' := e d
  let f := e.symm (B'.endpoint d')
  have hf : f ≠ d := by
    intro h
    apply B'.endpoint_ne d'
    have hh := congrArg e h
    simpa only [f, d', Equiv.apply_symm_apply] using hh
  have hs : B.step.SameCycle d.val f.val := by
    have ht : B'.step.SameCycle d'.val (B'.endpoint d').val :=
      (B'.sameCycle_endpoint_iff d' (B'.endpoint d')).mpr (Or.inr rfl)
    apply sameCycle_map_of_step B'.step B.step Subtype.val ?_ ht
    intro x
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have he := B.endpoint_eq_of_sameCycle d f hf hs
  have hh := congrArg e he
  change e (B.endpoint d) = B'.endpoint d'
  simpa only [f, Equiv.apply_symm_apply] using hh

variable (P : RibbonMap D) (hcap : ∀ d, B.cap d = P.edge d)
  (hr : ∀ d, p (P.rotation d) ↔ p d)
  (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)

include hc hcap in
theorem restricted_cap_invariant (d : D) : p (P.edge d) ↔ p d := by
  rw [← hcap]
  exact hc d

include hrot in
theorem restricted_rotation (d : {d : D // p d})
    (hd : (B.restricted p hc hb).corridor d ≠ d) :
    (P.restrict p (B.restricted_cap_invariant p hc P hcap) hr).rotation d =
      (B.restricted p hc hb).corridor d := by
  apply Subtype.ext
  exact hrot d.val (fun he ↦ hd (Subtype.ext he))

include hp in
theorem endpointRibbon_restrict_euler_iff [Finite D] :
    (Fintype.card (B.endpointRibbon P hrot).Vertex +
        Fintype.card (B.endpointRibbon P hrot).Face =
      Fintype.card (B.endpointRibbon P hrot).Edge +
        2 * Fintype.card (B.endpointRibbon P hrot).Component) ↔
    (Fintype.card ((B.restricted p hc hb).endpointRibbon
        (P.restrict p (B.restricted_cap_invariant p hc P hcap) hr)
        (B.restricted_rotation p hc hb P hcap hr hrot)).Vertex +
      Fintype.card ((B.restricted p hc hb).endpointRibbon
        (P.restrict p (B.restricted_cap_invariant p hc P hcap) hr)
        (B.restricted_rotation p hc hb P hcap hr hrot)).Face =
      Fintype.card ((B.restricted p hc hb).endpointRibbon
        (P.restrict p (B.restricted_cap_invariant p hc P hcap) hr)
        (B.restricted_rotation p hc hb P hcap hr hrot)).Edge +
      2 * Fintype.card ((B.restricted p hc hb).endpointRibbon
        (P.restrict p (B.restricted_cap_invariant p hc P hcap) hr)
        (B.restricted_rotation p hc hb P hcap hr hrot)).Component) := by
  apply RibbonMap.relabel_euler_iff _ _ (B.restrictedEndpointsEquiv p hc hb hp)
  · exact B.restrictedEndpointsEquiv_pairing p hc hb hp
  · intro d
    rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem
