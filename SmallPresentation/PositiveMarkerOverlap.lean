module

public import SmallPresentation.RelativeSmallCancellation

/-! # Short overlap for positive alternating marker rows with an optional coefficient -/
@[expose] public section

namespace SmallPresentationStatements.PositiveMarkerOverlap

structure Family (I : Type) where
  blocks : I → ℕ
  blocks_cases : ∀ i, blocks i = 32 ∨ blocks i = 33
  marker : ∀ i, Fin (blocks i) → ℕ
  marker_ge_two : ∀ i p, 2 ≤ marker i p
  marker_injective : Function.Injective (fun p : Σ i, Fin (blocks i) ↦ marker p.1 p.2)
  special : I → Bool

namespace Family
variable {I : Type} (F : Family I)

def length (i : I) : ℕ := 2 * F.blocks i + (F.special i).toNat

instance length_neZero (i : I) : NeZero (F.length i) := by
  constructor
  have h := F.blocks_cases i
  dsimp [length]
  omega

def IsMarker (i : I) (p : Fin (F.length i)) : Prop :=
  (F.special i).toNat ≤ p.val ∧ (p.val - (F.special i).toNat) % 2 = 1

instance isMarkerDecidable (i : I) (p : Fin (F.length i)) : Decidable (F.IsMarker i p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def coordinate (i : I) (p : Fin (F.length i)) : ℤ :=
  if h : p.val < (F.special i).toNat then 0
  else if (p.val - (F.special i).toNat) % 2 = 0 then 1
  else F.marker i ⟨(p.val - (F.special i).toNat) / 2, by
    have hp := p.isLt
    dsimp [length] at hp
    omega⟩

theorem coordinate_nonneg (i : I) (p : Fin (F.length i)) : 0 ≤ F.coordinate i p := by
  unfold coordinate
  split
  · omega
  · split <;> omega

theorem coordinate_ge_two_iff (i : I) (p : Fin (F.length i)) :
    2 ≤ F.coordinate i p ↔ F.IsMarker i p := by
  unfold coordinate IsMarker
  split
  · omega
  · split
    · omega
    · have h := F.marker_ge_two i ⟨(p.val - (F.special i).toNat) / 2, by
        have hp := p.isLt
        dsimp [length] at hp
        omega⟩
      omega

theorem marker_value (i : I) (p : Fin (F.length i)) (hp : F.IsMarker i p) :
    F.coordinate i p = F.marker i ⟨(p.val - (F.special i).toNat) / 2, by
      have h := p.isLt
      dsimp [length] at h
      have hp0 := hp.1
      omega⟩ := by
  have hp0 := hp.1
  simp only [coordinate, dite_eq_right (by omega : ¬p.val < (F.special i).toNat),
    hp.2, Nat.one_ne_zero, ite_false]

theorem marker_position_injective (i j : I) (p : Fin (F.length i)) (q : Fin (F.length j))
    (hp : 2 ≤ F.coordinate i p) (heq : F.coordinate i p = F.coordinate j q) :
    (⟨i, p⟩ : Σ i, Fin (F.length i)) = ⟨j, q⟩ := by
  have hq : 2 ≤ F.coordinate j q := heq ▸ hp
  have hpm := (F.coordinate_ge_two_iff i p).mp hp
  have hqm := (F.coordinate_ge_two_iff j q).mp hq
  rw [F.marker_value i p hpm, F.marker_value j q hqm] at heq
  have hm : (⟨i, ⟨(p.val - (F.special i).toNat) / 2, by
      have h := p.isLt
      have hp0 := hpm.1
      dsimp [length] at h
      omega⟩⟩ : Σ i, Fin (F.blocks i)) =
      ⟨j, ⟨(q.val - (F.special j).toNat) / 2, by
        have h := q.isLt
        have hq0 := hqm.1
        dsimp [length] at h
        omega⟩⟩ := F.marker_injective (Int.ofNat_inj.mp heq)
  have hij : i = j := congrArg Sigma.fst hm
  have hpos := congrArg (fun a : Σ i, Fin (F.blocks i) ↦ a.2.val) hm
  cases hij
  apply congrArg (Sigma.mk i)
  apply Fin.ext
  dsimp only at hpos
  have hp0 := hpm.1
  have hq0 := hqm.1
  have hp1 := hpm.2
  have hq1 := hqm.2
  omega

private theorem shape_covers (b : ℕ) (hb : b = 32 ∨ b = 33) (special : Bool)
    (forward : Bool) (p : Fin (2 * b + special.toNat)) :
    ∃ t : Fin 3,
      let q := if forward then (p.val + t.val) % (2 * b + special.toNat)
        else ((2 * b + special.toNat) - (p.val + t.val) % (2 * b + special.toNat)) %
          (2 * b + special.toNat)
      special.toNat ≤ q ∧ (q - special.toNat) % 2 = 1 := by
  rcases hb with rfl | rfl <;> cases special <;> revert forward p <;> decide

abbrev Origin := RelativeSmallCancellation.Origin F.length

def point (a : F.Origin) (t : ℕ) : Σ i, Fin (F.length i) :=
  ⟨a.row, if a.forward then a.position + Fin.ofNat (F.length a.row) t
    else -(a.position + Fin.ofNat (F.length a.row) t)⟩

def signedAt (a : F.Origin) (t : ℕ) : ℤ :=
  if a.forward then F.coordinate (F.point a t).1 (F.point a t).2
    else -F.coordinate (F.point a t).1 (F.point a t).2

theorem triple_has_marker (a : F.Origin) :
    ∃ t : Fin 3, 2 ≤ F.coordinate (F.point a t.val).1 (F.point a t.val).2 := by
  obtain ⟨t, ht⟩ := shape_covers (F.blocks a.row) (F.blocks_cases a.row)
    (F.special a.row) a.forward a.position
  refine ⟨t, (F.coordinate_ge_two_iff _ _).mpr ?_⟩
  have hv : (F.point a t.val).2.val =
      if a.forward then (a.position.val + t.val) % F.length a.row
      else (F.length a.row - (a.position.val + t.val) % F.length a.row) % F.length a.row := by
    cases hs : a.forward
    · simp only [point, hs, Bool.false_eq_true, ite_false]
      change (F.length a.row - (a.position.val + t.val % F.length a.row) % F.length a.row) %
        F.length a.row = _
      simp only [Nat.add_mod_mod]
    · simp only [point, hs, ite_true]
      change (a.position.val + t.val % F.length a.row) % F.length a.row = _
      simp only [Nat.add_mod_mod]
  change (F.special a.row).toNat ≤ (F.point a t.val).2.val ∧
    ((F.point a t.val).2.val - (F.special a.row).toNat) % 2 = 1
  rw [hv]
  exact ht

private theorem signed_injective (x y : ℤ) (hx : 2 ≤ x) (hy : 0 ≤ y)
    (a b : Bool) (h : (if a then x else -x) = (if b then y else -y)) : a = b ∧ x = y := by
  cases a <;> cases b <;> simp_all <;> omega

/-- A single large positive marker in a matching triple recovers row, orientation, and position. -/
theorem triple_injective (a b : F.Origin)
    (h : ∀ t : Fin 3, F.signedAt a t.val = F.signedAt b t.val) : a = b := by
  obtain ⟨t, ht⟩ := F.triple_has_marker a
  have hy := F.coordinate_nonneg (F.point b t.val).1 (F.point b t.val).2
  obtain ⟨hs, heq⟩ := signed_injective _ _ ht hy a.forward b.forward (h t)
  have hpoint := F.marker_position_injective _ _ _ _ ht heq
  have hrow : a.row = b.row := congrArg Sigma.fst hpoint
  rcases a with ⟨i, s, p⟩
  rcases b with ⟨j, s', q⟩
  dsimp only at hs hrow
  cases hrow
  cases hs
  have hfin : (F.point ⟨i, s, p⟩ t.val).2 = (F.point ⟨i, s, q⟩ t.val).2 :=
    eq_of_heq (Sigma.ext_iff.mp hpoint).2
  have hpq : p = q := by
    cases s
    · change -(p + Fin.ofNat (F.length i) t.val) = -(q + Fin.ofNat (F.length i) t.val) at hfin
      exact add_right_cancel (neg_injective hfin)
    · change p + Fin.ofNat (F.length i) t.val = q + Fin.ofNat (F.length i) t.val at hfin
      exact add_right_cancel hfin
  cases hpq
  rfl

end Family
end SmallPresentationStatements.PositiveMarkerOverlap
