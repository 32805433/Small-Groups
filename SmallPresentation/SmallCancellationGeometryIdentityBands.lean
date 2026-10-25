module

public import SmallPresentation.SmallCancellationGeometryIdentityDarts

/-!
# Suppressing corridor interiors by finite alternating paths

A cap pairing and a corridor involution act on the same finite incidence set. Corridor
fixed points are the relator incidences. Alternating between cap and corridor edges
induces a genuine fixed-point-free involution on those incidences. The construction
uses the least positive return of a finite permutation, and proves reversal of its
actual paths. Inverse labels at the endpoints follow by following the same paths.
No planar or Euler-characteristic hypothesis is needed for this finite suppression.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

/-- Two involutions describing the cap arcs and the pairs of corridor sides. -/
structure BandSystem (D X : Type*) where
  cap : Equiv.Perm D
  corridor : Equiv.Perm D
  cap_involutive : Function.Involutive cap
  corridor_involutive : Function.Involutive corridor
  letter : D → SignedLetter X
  cap_letter : ∀ d, letter (cap d) = reverseLetter (letter d)
  corridor_letter : ∀ d, corridor d ≠ d → letter (corridor d) = reverseLetter (letter d)

namespace BandSystem

attribute [local instance] Classical.propDecidable

variable {D X : Type*} (B : BandSystem D X)

/-- One cap edge followed by one corridor identification. -/
def step : Equiv.Perm D := B.cap.trans B.corridor

/-- The relator-boundary incidences left unpaired by corridor identification. -/
abbrev Endpoint := {d : D // B.corridor d = d}

/-- Reversing a single alternating step reverses its two sides in the other order. -/
theorem reverse_step (d : D) : B.step (B.corridor (B.step d)) = B.corridor d := by
  change B.corridor (B.cap (B.corridor (B.corridor (B.cap d)))) = B.corridor d
  rw [B.corridor_involutive, B.cap_involutive]

/-- Reversal of an actual finite alternating path, including its endpoints. -/
theorem reverse_walk (n m : ℕ) (d : D) :
    B.step^[n] (B.corridor (B.step^[n + m] d)) = B.corridor (B.step^[m] d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + m = n + m + 1 by omega]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', B.reverse_step]
    exact ih

variable [Finite D]

/-- Every endpoint has a positive return to the endpoint set, by finiteness. -/
theorem exists_return (d : B.Endpoint) :
    ∃ n : ℕ, 0 < n ∧ B.corridor (B.step^[n] d.val) = B.step^[n] d.val := by
  refine ⟨Function.minimalPeriod B.step d.val, ?_, ?_⟩
  · exact Function.minimalPeriod_pos_of_mem_periodicPts (B.step.injective.mem_periodicPts d.val)
  · rw [Function.iterate_minimalPeriod]
    exact d.property

/-- First positive return to a relator incidence along the actual alternating path. -/
noncomputable def returnTime (d : B.Endpoint) : ℕ := Nat.find (B.exists_return d)

theorem returnTime_pos (d : B.Endpoint) : 0 < B.returnTime d :=
  (Nat.find_spec (B.exists_return d)).1

theorem returnTime_fixed (d : B.Endpoint) :
    B.corridor (B.step^[B.returnTime d] d.val) = B.step^[B.returnTime d] d.val :=
  (Nat.find_spec (B.exists_return d)).2

theorem no_early_return (d : B.Endpoint) (j : ℕ) (hj : 0 < j) (hlt : j < B.returnTime d) :
    B.corridor (B.step^[j] d.val) ≠ B.step^[j] d.val := by
  intro he
  have := Nat.find_min' (B.exists_return d) ⟨hj, he⟩
  exact (Nat.not_le_of_gt hlt) this

/-- The other endpoint reached by this finite alternating path. -/
noncomputable def endpoint (d : B.Endpoint) : B.Endpoint :=
  ⟨B.step^[B.returnTime d] d.val, B.returnTime_fixed d⟩

/-- Reversing the first-return path reaches the original endpoint in the same number of steps. -/
theorem return_walk (d : B.Endpoint) :
    B.step^[B.returnTime d] (B.endpoint d).val = d.val := by
  have h := B.reverse_walk (B.returnTime d) 0 d.val
  simpa only [Nat.add_zero, Function.iterate_zero, id_eq, B.returnTime_fixed, d.property,
    endpoint] using h

/-- A partial reverse traversal corresponds to the complementary forward traversal. -/
theorem reverse_initial (d : B.Endpoint) (j : ℕ) (hj : j ≤ B.returnTime d) :
    B.step^[j] (B.endpoint d).val =
      B.corridor (B.step^[B.returnTime d - j] d.val) := by
  have h := B.reverse_walk j (B.returnTime d - j) d.val
  rw [Nat.add_sub_of_le hj, B.returnTime_fixed] at h
  exact h

/-- A first-return path has no new intermediate endpoint when traversed backwards. -/
theorem returnTime_endpoint (d : B.Endpoint) : B.returnTime (B.endpoint d) = B.returnTime d := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    refine ⟨B.returnTime_pos d, ?_⟩
    rw [B.return_walk]
    exact d.property
  · by_contra hn
    have hlt : B.returnTime (B.endpoint d) < B.returnTime d := by omega
    have hpos := B.returnTime_pos (B.endpoint d)
    have hr := B.returnTime_fixed (B.endpoint d)
    rw [B.reverse_initial d _ (Nat.le_of_lt hlt), B.corridor_involutive] at hr
    apply B.no_early_return d (B.returnTime d - B.returnTime (B.endpoint d)) (by omega) (by omega)
    exact hr.symm

/-- Suppressed alternating bands reverse involutively at their two relator incidences. -/
theorem endpoint_involutive : Function.Involutive B.endpoint := by
  intro d
  apply Subtype.ext
  change B.step^[B.returnTime (B.endpoint d)] (B.endpoint d).val = d.val
  rw [B.returnTime_endpoint, B.return_walk]

/-- Before the final endpoint, each cap flip is followed by a corridor flip. -/
theorem interior_letter (d : B.Endpoint) (j : ℕ) (hj : j < B.returnTime d) :
    B.letter (B.step^[j] d.val) = B.letter d.val := by
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
    change B.letter (B.corridor (B.cap (B.step^[j] d.val))) = _
    rw [B.corridor_letter _ hc, B.cap_letter, reverseLetter_reverseLetter]
    exact ih (by omega)

/-- The final cap contributes one uncancelled sign reversal at the other endpoint. -/
theorem endpoint_letter (d : B.Endpoint) :
    B.letter (B.endpoint d).val = reverseLetter (B.letter d.val) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (B.returnTime_pos d))
  have hfix := B.returnTime_fixed d
  rw [hj, Function.iterate_succ_apply'] at hfix
  change B.corridor (B.corridor (B.cap (B.step^[j] d.val))) =
    B.corridor (B.cap (B.step^[j] d.val)) at hfix
  rw [B.corridor_involutive] at hfix
  change B.letter (B.step^[B.returnTime d] d.val) = _
  rw [hj, Function.iterate_succ_apply']
  change B.letter (B.corridor (B.cap (B.step^[j] d.val))) = _
  rw [← hfix, B.cap_letter, B.interior_letter d j (by omega)]

/-- A signed letter is never its own inverse, so the two endpoints of a band are distinct. -/
theorem endpoint_ne (d : B.Endpoint) : B.endpoint d ≠ d := by
  intro he
  have hl := B.endpoint_letter d
  rw [he] at hl
  have hs := congrArg Prod.snd hl
  change (B.letter d.val).2 = !(B.letter d.val).2 at hs
  cases h : (B.letter d.val).2 <;> simp [h] at hs

/-- Actual arc pairing after suppressing all corridor interiors. -/
noncomputable def endpointPairing : Equiv.Perm B.Endpoint where
  toFun := B.endpoint
  invFun := B.endpoint
  left_inv := B.endpoint_involutive
  right_inv := B.endpoint_involutive

end BandSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
