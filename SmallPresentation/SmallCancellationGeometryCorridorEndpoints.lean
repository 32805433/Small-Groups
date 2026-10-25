module

public import SmallPresentation.SmallCancellationGeometryIdentityBands
public import SmallPresentation.PermutationCycleDeletion

/-!
# Alternating orbits determine the two ends of a corridor

Each alternating permutation orbit containing a relator dart contains exactly
its two paired endpoints. This characterizes the first-return pairing solely
by orbit membership and is stable under removal of interior darts.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem

variable {D X : Type*} [Finite D] (B : BandSystem D X)

theorem twice_return_periodic (d : B.Endpoint) :
    Function.IsPeriodicPt B.step (2 * B.returnTime d) d.val := by
  change B.step^[2 * B.returnTime d] d.val = d.val
  rw [two_mul, Function.iterate_add_apply]
  exact B.return_walk d

/-- In its full alternating orbit, the only fixed corridor darts are the two ends. -/
theorem endpoint_of_sameCycle (d e : B.Endpoint) (h : B.step.SameCycle d.val e.val) :
    e = d ∨ e = B.endpoint d := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hp := B.twice_return_periodic d
  have hn' : B.step^[n % (2 * B.returnTime d)] d.val = e.val := by
    rw [hp.iterate_mod_apply]
    simpa only [Equiv.Perm.coe_pow] using hn
  let j := n % (2 * B.returnTime d)
  have hj : j < 2 * B.returnTime d := Nat.mod_lt _ (by have := B.returnTime_pos d; omega)
  by_cases hzero : j = 0
  · left
    apply Subtype.ext
    simpa only [j, hzero, Function.iterate_zero, id_eq] using hn'.symm
  · by_cases hfirst : j < B.returnTime d
    · exfalso
      apply B.no_early_return d j (by omega) hfirst
      change B.corridor (B.step^[n % (2 * B.returnTime d)] d.val) = _
      rw [hn']
      exact e.property
    · have hj' : j - B.returnTime d < B.returnTime (B.endpoint d) := by
        rw [B.returnTime_endpoint]
        omega
      have hx : B.step^[j - B.returnTime d] (B.endpoint d).val = e.val := by
        change B.step^[j - B.returnTime d] (B.step^[B.returnTime d] d.val) = e.val
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hn'
      by_cases heq : j = B.returnTime d
      · right
        apply Subtype.ext
        simpa only [heq, Nat.sub_self, Function.iterate_zero, id_eq] using hx.symm
      · exfalso
        apply B.no_early_return (B.endpoint d) (j - B.returnTime d) (by omega) hj'
        rw [hx]
        exact e.property

theorem sameCycle_endpoint_iff (d e : B.Endpoint) :
    B.step.SameCycle d.val e.val ↔ e = d ∨ e = B.endpoint d := by
  constructor
  · exact B.endpoint_of_sameCycle d e
  · rintro (rfl | rfl)
    · exact .refl _ _
    · exact ⟨(B.returnTime d : ℤ), by
        rw [zpow_natCast, Equiv.Perm.coe_pow]
        rfl⟩

/-- A distinct endpoint in the same alternating orbit is necessarily the first-return partner. -/
theorem endpoint_eq_of_sameCycle (d e : B.Endpoint) (hne : e ≠ d)
    (h : B.step.SameCycle d.val e.val) : B.endpoint d = e := by
  exact ((B.endpoint_of_sameCycle d e h).resolve_left hne).symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem
