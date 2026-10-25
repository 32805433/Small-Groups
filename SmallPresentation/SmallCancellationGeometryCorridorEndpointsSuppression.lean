module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpoints
public import SmallPresentation.SmallCancellationGeometryCorridorSuppression

/-!
# Suppressing one corridor preserves the actual endpoint pairing

The reconnected cap edges traverse the same alternating bands. The first-return
pairing is consequently unchanged on every surviving relator incidence.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.DegreeTwoVertex

open PermutationCycles

variable {D X : Type*} {P : RibbonMap D} (C : DegreeTwoVertex P)

open Classical in
theorem edge_val (d : C.Dart) :
    (C.suppress.edge d).val =
      if d.val = P.edge C.left then P.edge C.right
      else if d.val = P.edge C.right then P.edge C.left else P.edge d.val := by
  classical
  by_cases hl : d.val = P.edge C.left
  · rw [ite_eq_left hl]
    have hd : d = C.dualBigon.leftDart := Subtype.ext hl
    rw [hd, suppress_edge, Bigon.edge_leftDart]
    rfl
  · rw [ite_eq_right hl]
    by_cases hr : d.val = P.edge C.right
    · rw [ite_eq_left hr]
      have hd : d = C.dualBigon.rightDart := Subtype.ext hr
      rw [hd, suppress_edge, Bigon.edge_rightDart]
      rfl
    · rw [ite_eq_right hr]
      exact C.dualBigon.edge_val_of_ne d hl hr

variable (B : BandSystem D X) (hcap : ∀ d, B.cap d = P.edge d)
  (hleft : B.corridor C.left = C.right)

include hleft in
theorem corridor_right : B.corridor C.right = C.left := by
  rw [← hleft, B.corridor_involutive]

include hleft in
theorem corridor_survives (d : D) :
    (B.corridor d ≠ C.left ∧ B.corridor d ≠ C.right) ↔
      (d ≠ C.left ∧ d ≠ C.right) := by
  rw [← C.corridor_right B hleft, ← hleft,
    B.corridor.injective.ne_iff, B.corridor.injective.ne_iff]
  rw [B.corridor_involutive]
  exact and_comm

noncomputable def suppressedCorridor : Equiv.Perm C.Dart :=
  C.dartEquiv.trans ((B.corridor.subtypePerm (C.corridor_survives B hleft)).trans C.dartEquiv.symm)

@[simp] theorem suppressedCorridor_val (d : C.Dart) :
    (C.suppressedCorridor B hleft d).val = B.corridor d.val := rfl

theorem suppressedCorridor_involutive : Function.Involutive (C.suppressedCorridor B hleft) := by
  intro d
  apply Subtype.ext
  exact B.corridor_involutive d.val

include hcap hleft in
theorem suppressed_cap_letter (d : C.Dart) :
    B.letter (C.suppress.edge d).val = reverseLetter (B.letter d.val) := by
  classical
  have hletter (x : D) : B.letter (P.edge x) = reverseLetter (B.letter x) := by
    rw [← hcap]
    exact B.cap_letter x
  have hc : B.letter C.right = reverseLetter (B.letter C.left) := by
    rw [← hleft]
    exact B.corridor_letter C.left (by rw [hleft]; exact C.ne.symm)
  rw [C.edge_val]
  split_ifs with hl hr
  · rw [hl, hletter, hletter, hc, reverseLetter_reverseLetter]
  · rw [hr, hletter, hletter, hc, reverseLetter_reverseLetter]
  · exact hletter _

noncomputable def suppressedBands : BandSystem C.Dart X where
  cap := C.suppress.edge
  corridor := C.suppressedCorridor B hleft
  cap_involutive := C.suppress.edge_involutive
  corridor_involutive := C.suppressedCorridor_involutive B hleft
  letter d := B.letter d.val
  cap_letter := C.suppressed_cap_letter B hcap hleft
  corridor_letter d hd := B.corridor_letter d.val (fun he ↦ hd (Subtype.ext he))

/-- All original endpoints survive the deletion of a moving corridor pair. -/
def endpointSurvives (d : B.Endpoint) : C.Dart :=
  C.dartEquiv.symm ⟨d.val, by
    constructor
    · intro he
      have hh := d.property
      rw [he, hleft] at hh
      exact C.ne hh.symm
    · intro he
      have hh := d.property
      rw [he, C.corridor_right B hleft] at hh
      exact C.ne hh⟩

/-- Exact identification of the endpoint incidences before and after suppression. -/
def endpointsEquiv : B.Endpoint ≃ (C.suppressedBands B hcap hleft).Endpoint where
  toFun d := ⟨C.endpointSurvives B hleft d, Subtype.ext d.property⟩
  invFun d := ⟨d.val.val, congrArg Subtype.val d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A reconnected alternating step makes one or two original alternating steps. -/
theorem suppressed_step_sameCycle (d : C.Dart) :
    B.step.SameCycle d.val ((C.suppressedBands B hcap hleft).step d).val := by
  classical
  change B.step.SameCycle d.val (B.corridor (C.suppress.edge d).val)
  rw [C.edge_val]
  split_ifs with hl hr
  · have hs : B.step d.val = C.right := by
      change B.corridor (B.cap d.val) = C.right
      rw [hcap, hl, P.edge_involutive, hleft]
    have ht : B.step (B.step d.val) = B.corridor (P.edge C.right) := by
      rw [hs]
      exact congrArg B.corridor (hcap C.right)
    rw [← ht]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  · have hs : B.step d.val = C.left := by
      change B.corridor (B.cap d.val) = C.left
      rw [hcap, hr, P.edge_involutive, C.corridor_right B hleft]
    have ht : B.step (B.step d.val) = B.corridor (P.edge C.left) := by
      rw [hs]
      exact congrArg B.corridor (hcap C.left)
    rw [← ht]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  · have hs : B.step d.val = B.corridor (P.edge d.val) := congrArg B.corridor (hcap d.val)
    rw [← hs]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- The finite first-return endpoint pairing is literally unchanged under one suppression. -/
theorem endpointsEquiv_pairing [Finite D] (d : B.Endpoint) :
    C.endpointsEquiv B hcap hleft (B.endpointPairing d) =
      (C.suppressedBands B hcap hleft).endpointPairing (C.endpointsEquiv B hcap hleft d) := by
  let B' := C.suppressedBands B hcap hleft
  let e := C.endpointsEquiv B hcap hleft
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
    exact sameCycle_map_of_step B'.step B.step Subtype.val
      (C.suppressed_step_sameCycle B hcap hleft) ht
  have he := B.endpoint_eq_of_sameCycle d f hf hs
  have hh := congrArg e he
  change e (B.endpoint d) = B'.endpoint d'
  simpa only [f, Equiv.apply_symm_apply] using hh

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.DegreeTwoVertex
