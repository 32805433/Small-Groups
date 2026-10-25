module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsRestriction

/-!
# Suppression of all corridor interiors preserves spherical Euler characteristic

Induction deletes actual degree-two vertices. An isolated closed band is discarded
as an invariant endpoint-free component; every other deletion reconnects its two
edges. Both operations preserve the exact first-return ribbon on the retained darts.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

abbrev EulerEquality {D : Type*} [Finite D] (P : RibbonMap D) : Prop :=
  Fintype.card P.Vertex + Fintype.card P.Face =
    Fintype.card P.Edge + 2 * Fintype.card P.Component

end RibbonMap

namespace BandSystem

universe u v

variable {D : Type u} {X : Type v} (B : BandSystem D X)

include B in
theorem endpoint_val_of_all_fixed [Finite D] (hfix : ∀ d, B.corridor d = d)
    (d : B.Endpoint) : (B.endpointPairing d).val = B.cap d.val := by
  classical
  have ht : B.returnTime d = 1 := by
    have hle : B.returnTime d ≤ 1 := Nat.find_min' (B.exists_return d) ⟨by decide, hfix _⟩
    have hp := B.returnTime_pos d
    omega
  change B.step^[B.returnTime d] d.val = B.cap d.val
  rw [ht]
  exact hfix _

noncomputable def allEndpointsEquiv (hfix : ∀ d, B.corridor d = d) : B.Endpoint ≃ D where
  toFun := Subtype.val
  invFun d := ⟨d, hfix d⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem endpointRibbon_euler_of_all_fixed [Finite D] (P : RibbonMap D)
    (hcap : ∀ d, B.cap d = P.edge d)
    (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)
    (hfix : ∀ d, B.corridor d = d) (hEuler : P.EulerEquality) :
    (B.endpointRibbon P hrot).EulerEquality := by
  apply ((B.endpointRibbon P hrot).relabel_euler_iff P (B.allEndpointsEquiv hfix) ?_ ?_).mpr hEuler
  · intro d
    exact (B.endpoint_val_of_all_fixed hfix d).trans (hcap d.val)
  · intro d
    rfl

private theorem endpointRibbon_euler_aux (n : ℕ) :
    ∀ (D : Type u) (_ : Fintype D) (B : BandSystem D X) (P : RibbonMap D)
      (_hcap : ∀ d, B.cap d = P.edge d)
      (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d),
      Fintype.card D = n → P.EulerEquality → (B.endpointRibbon P hrot).EulerEquality := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D inst B P hcap hrot hn hEuler
    classical
    by_cases hfix : ∀ d, B.corridor d = d
    · exact B.endpointRibbon_euler_of_all_fixed P hcap hrot hfix hEuler
    · push Not at hfix
      obtain ⟨a, ha⟩ := hfix
      let b := B.corridor a
      have hab : a ≠ b := ha.symm
      have hba : B.corridor b = a := B.corridor_involutive a
      have hb : B.corridor b ≠ b := by rw [hba]; exact hab
      have hr₁ : P.rotation a = b := hrot a ha
      have hr₂ : P.rotation b = a := (hrot b hb).trans hba
      by_cases he : P.edge a = b
      · let p : D → Prop := fun d ↦ d ≠ a ∧ d ≠ b
        have hpair (σ : Equiv.Perm D) (h₁ : σ a = b) (h₂ : σ b = a) (d : D) :
            p (σ d) ↔ p d := by
          simpa only [p, not_or] using
            not_congr (PermutationCycles.twoCycle_invariant σ a b h₁ h₂ d)
        have hedge : ∀ d, p (P.edge d) ↔ p d :=
          hpair P.edge he (by rw [← he, P.edge_involutive])
        have hcorr : ∀ d, p (B.corridor d) ↔ p d := hpair B.corridor rfl hba
        have hrotation : ∀ d, p (P.rotation d) ↔ p d := hpair P.rotation hr₁ hr₂
        have hcap' : ∀ d, p (B.cap d) ↔ p d := by intro d; rw [hcap]; exact hedge d
        have hp : ∀ d : B.Endpoint, p d.val := by
          intro d
          constructor
          · intro hd
            exact ha (hd ▸ d.property)
          · intro hd
            exact hb (hd ▸ d.property)
        let B' := B.restricted p hcap' hcorr
        let P' := P.restrict p (B.restricted_cap_invariant p hcap' P hcap) hrotation
        have hcap'' (d : {d : D // p d}) : B'.cap d = P'.edge d := Subtype.ext (hcap d.val)
        have hrot' := B.restricted_rotation p hcap' hcorr P hcap hrotation hrot
        have hlt : Fintype.card {d : D // p d} < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := a) (fun h ↦ h.1 rfl)
        have hE : P'.EulerEquality := P.restrict_euler p
          (B.restricted_cap_invariant p hcap' P hcap) hrotation hEuler
        have hi := ih _ hlt _ inferInstance B' P' hcap'' hrot' rfl hE
        exact (B.endpointRibbon_restrict_euler_iff p hcap' hcorr hp P hcap hrotation hrot).mpr hi
      · let C : DegreeTwoVertex P := ⟨a, b, hab, hr₁, hr₂, he⟩
        have hl : B.corridor C.left = C.right := rfl
        let B' := C.suppressedBands B hcap hl
        have hcap' (d : C.Dart) : B'.cap d = C.suppress.edge d := rfl
        have hrot' := C.suppressed_rotation B hcap hl hrot
        have hlt : Fintype.card C.Dart < n := by
          have hh : Fintype.card D = Fintype.card C.Dart + 2 := by
            simpa only [Fintype.card_eq_nat_card] using C.dualBigon.card_darts
          omega
        have hE : C.suppress.EulerEquality := C.euler_iff.mpr hEuler
        have hi := ih _ hlt _ inferInstance B' C.suppress hcap' hrot' rfl hE
        exact (C.endpointRibbon_suppress_euler_iff B hcap hl hrot).mpr hi

/-- All corridor interiors may be suppressed, discarding closed bands without endpoints,
without changing spherical Euler characteristic of the induced first-return ribbon. -/
theorem endpointRibbon_euler [Fintype D] (P : RibbonMap D)
    (hcap : ∀ d, B.cap d = P.edge d)
    (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)
    (hEuler : P.EulerEquality) : (B.endpointRibbon P hrot).EulerEquality :=
  endpointRibbon_euler_aux (Fintype.card D) D inferInstance B P hcap hrot rfl hEuler

end BandSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
