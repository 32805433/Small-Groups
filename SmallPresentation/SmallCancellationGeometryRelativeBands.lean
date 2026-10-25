module

public import SmallPresentation.SmallCancellationGeometryRibbonCounts
public import SmallPresentation.SmallCancellationAugmentationWords

/-!
# Reading actual opposite bands as semi-initial pieces

A band records consecutive incidences in opposite vertex directions and actual edge matches.
The two-step face equations between consecutive matched arcs supply equality of the internal
coefficients. The final positive incidence supplies only its factor tag, exactly as required
by the semi-initial convention.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonLabelling

variable {D X H : Type*} [Group H] {P : RibbonMap D}

/-- A one- or two-corner face with coefficient product one gives the corresponding two-term
equation. If the corners coincide, the one-corner equation makes each term one. -/
theorem two_step_face_equation (L : RibbonLabelling P X H) (d e : D)
    (h₁ : P.face d = e) (h₂ : P.face e = d) (hface : L.faceValue d = 1) :
    L.corner d * L.corner e = 1 := by
  by_cases he : d = e
  · cases he
    have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr h₁
    have hc : L.corner d = 1 := by
      simpa [faceValue, RibbonMap.faceBoundary, hp] using hface
    simp [hc]
  · have hperiodic : Function.IsPeriodicPt P.face 2 d := by
      change P.face (P.face d) = d
      rw [h₁, h₂]
    have hle := hperiodic.minimalPeriod_le (by decide : 0 < 2)
    have hpos := hperiodic.minimalPeriod_pos (by decide : 0 < 2)
    have hne : Function.minimalPeriod P.face d ≠ 1 := by
      intro hp
      have hh := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hp
      exact he (hh.symm.trans h₁)
    have hp : Function.minimalPeriod P.face d = 2 := by omega
    have hh : (L.corner d)⁻¹ * (L.corner e)⁻¹ = 1 := by
      simpa [faceValue, RibbonMap.faceBoundary, hp, List.ofFn_succ, h₁] using hface
    exact mul_eq_one_comm.mp (by
      simpa only [mul_inv_rev, inv_inv, inv_one] using congrArg Inv.inv hh)

end RibbonLabelling

/-- A finite interval of consecutive opposite edge ends. All laws are stated on actual dart
incidences; no piece or metric conclusion is included in this data. -/
structure OppositeBand {D : Type*} (P : RibbonMap D) (n : ℕ) where
  upper : ℕ → D
  lower : ℕ → D
  upper_step : ∀ k, k + 1 < n → P.rotation (upper k) = upper (k + 1)
  lower_step : ∀ k, k + 1 < n → P.rotation (lower (k + 1)) = lower k
  edge_match : ∀ k, k < n → P.edge (upper k) = lower k
  upper_injective : Function.Injective (fun k : Fin n ↦ upper k.val)
  lower_injective : Function.Injective (fun k : Fin n ↦ lower k.val)

namespace OppositeBand

variable {D X H : Type*} {P : RibbonMap D} {n : ℕ} (B : OppositeBand P n)

/-- The two corners between consecutive band arcs are consecutive in their actual face. -/
theorem face_upper (k : ℕ) (hk : k + 1 < n) :
    P.face (B.upper k) = B.lower (k + 1) := by
  apply P.rotation.injective
  rw [RibbonMap.face_apply, Equiv.apply_symm_apply, B.lower_step k hk,
    B.edge_match k (by omega)]

theorem face_lower (k : ℕ) (hk : k + 1 < n) :
    P.face (B.lower (k + 1)) = B.upper k := by
  apply P.rotation.injective
  rw [RibbonMap.face_apply, Equiv.apply_symm_apply, ← B.edge_match (k + 1) hk,
    P.edge_involutive, B.upper_step k hk]

/-- The relative face relation gives inverse coefficients along each internal band corner. -/
theorem corner_equation [Group H] (L : RibbonLabelling P X H)
    (k : ℕ) (hk : k + 1 < n) (hface : L.faceValue (B.upper k) = 1) :
    L.corner (B.upper k) * L.corner (B.lower (k + 1)) = 1 :=
  L.two_step_face_equation _ _ (B.face_upper k hk) (B.face_lower k hk) hface

theorem upper_iterate (k : ℕ) (hk : k < n) : B.upper k = P.rotation^[k] (B.upper 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← B.upper_step k hk, ih (by omega), Function.iterate_succ_apply']

theorem lower_iterate (k : ℕ) (hk : k < n) :
    B.lower k = P.rotation.symm^[k] (B.lower 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs : B.lower (k + 1) = P.rotation.symm (B.lower k) := by
      apply P.rotation.injective
      rw [B.lower_step k hk, Equiv.apply_symm_apply]
    rw [hs, ih (by omega), Function.iterate_succ_apply']

/-- An embedded band cannot traverse its upper vertex more than once. -/
theorem length_le_upper_vertex [Finite D] : n ≤ (P.vertexBoundary (B.upper 0)).length := by
  classical
  let l := List.ofFn (fun k : Fin n ↦ B.upper k.val)
  have hnd : l.Nodup := List.nodup_ofFn.mpr B.upper_injective
  have hs : l.toFinset ⊆ (P.vertexBoundary (B.upper 0)).toFinset := by
    intro d hd
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hd)
    apply List.mem_toFinset.mpr
    apply (P.mem_vertexBoundary_iff _ _).mpr
    rw [B.upper_iterate k.val k.isLt]
    change P.rotation.SameCycle (B.upper 0) ((P.rotation ^ k.val) (B.upper 0))
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hnd,
    List.toFinset_card_of_nodup (P.vertexBoundary_nodup _)] at hc
  simpa only [l, List.length_ofFn] using hc

/-- The same no-repetition bound holds at the oppositely traversed peripheral vertex. -/
theorem length_le_lower_vertex [Finite D] : n ≤ (P.vertexBoundary (B.lower 0)).length := by
  classical
  let l := List.ofFn (fun k : Fin n ↦ B.lower k.val)
  have hnd : l.Nodup := List.nodup_ofFn.mpr B.lower_injective
  have hs : l.toFinset ⊆ (P.vertexBoundary (B.lower 0)).toFinset := by
    intro d hd
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hd)
    apply List.mem_toFinset.mpr
    apply (P.mem_vertexBoundary_iff _ _).mpr
    rw [B.lower_iterate k.val k.isLt]
    change P.rotation.SameCycle (B.lower 0) ((P.rotation⁻¹ ^ k.val) (B.lower 0))
    apply Equiv.Perm.SameCycle.of_inv
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hnd,
    List.toFinset_card_of_nodup (P.vertexBoundary_nodup _)] at hc
  simpa only [l, List.length_ofFn] using hc

end OppositeBand

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
