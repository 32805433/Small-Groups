module

public import SmallPresentation.SmallCancellationGeometryIdentityBands

/-!
# Quotient path potentials through actual alternating bands

A potential records the group value of a path immediately before each incidence. Crossing
a cap, or a non-fixed corridor side, multiplies this value by the incidence label. Interior
cap/corridor pairs therefore cancel. The theorem is about the actual first-return endpoint
pairing, so it can be applied directly to the constructed relator ribbon.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem

variable {D X Q : Type*} [Finite D] [Group Q] (B : BandSystem D X)
    (read : SignedLetter X → Q) (hread : ∀ x, read (reverseLetter x) = (read x)⁻¹)
    (f : D → Q)
    (hcap : ∀ d, f (B.cap d) = f d * read (B.letter d))
    (hcorridor : ∀ d, B.corridor d ≠ d →
      f (B.corridor d) = f d * read (B.letter d))

include hread hcap hcorridor

/-- Every interior alternating step preserves the actual path potential. -/
theorem interior_potential (d : B.Endpoint) (j : ℕ) (hj : j < B.returnTime d) :
    f (B.step^[j] d.val) = f d.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hn := B.no_early_return d (j + 1) (by omega) hj
    have hc : B.corridor (B.cap (B.step^[j] d.val)) ≠ B.cap (B.step^[j] d.val) := by
      intro he
      apply hn
      rw [Function.iterate_succ_apply']
      change B.corridor (B.corridor (B.cap (B.step^[j] d.val))) =
        B.corridor (B.cap (B.step^[j] d.val))
      rw [B.corridor_involutive, he]
    rw [Function.iterate_succ_apply']
    change f (B.corridor (B.cap (B.step^[j] d.val))) = _
    rw [hcorridor _ hc, hcap, B.cap_letter, hread, mul_assoc, mul_inv_cancel, mul_one]
    exact ih (by omega)

/-- The final cap is the sole remaining label in the path-potential formula. -/
theorem endpoint_potential (d : B.Endpoint) :
    f (B.endpoint d).val = f d.val * read (B.letter d.val) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (B.returnTime_pos d))
  have hfix := B.returnTime_fixed d
  rw [hj, Function.iterate_succ_apply'] at hfix
  change B.corridor (B.corridor (B.cap (B.step^[j] d.val))) =
    B.corridor (B.cap (B.step^[j] d.val)) at hfix
  rw [B.corridor_involutive] at hfix
  change f (B.step^[B.returnTime d] d.val) = _
  rw [hj, Function.iterate_succ_apply']
  change f (B.corridor (B.cap (B.step^[j] d.val))) = _
  rw [← hfix, hcap, B.interior_letter d j (by omega),
    B.interior_potential read hread f hcap hcorridor d j (by omega)]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem
