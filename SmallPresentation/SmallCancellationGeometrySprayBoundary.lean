module

public import SmallPresentation.SmallCancellationGeometryPairingRibbon

/-!
# Exact free-group prefix potentials on cap pairings

The two endpoints of every actual cap have prefix values differing by precisely the
signed letter crossed. This is proved from the cap-insertion construction, not inferred
from inverse labels alone.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {X : Type*}

/-- Value of the path before a specified position in a boundary word. -/
def prefixValue (w : List (SignedLetter X)) (i : ℕ) : FreeGroup X := FreeGroup.mk (w.take i)

/-- The group element read by one oriented generator incidence. -/
def letterValue (x : SignedLetter X) : FreeGroup X := FreeGroup.mk [x]

theorem letterValue_reverse (x : SignedLetter X) :
    letterValue (reverseLetter x) = (letterValue x)⁻¹ := by
  rw [letterValue, letterValue, FreeGroup.inv_mk]
  rfl

theorem prefixValue_succ (w : List (SignedLetter X)) (i : Fin w.length) :
    prefixValue w (i.val + 1) = prefixValue w i.val * letterValue w[i] := by
  rw [prefixValue, prefixValue, letterValue, FreeGroup.mul_mk]
  exact congrArg FreeGroup.mk (List.take_append_getElem i.isLt).symm

namespace BoundaryPairing

private theorem prefix_insert_after (before after : List (SignedLetter X)) (x : X)
    (sign : Bool) (n : ℕ) (hn : before.length ≤ n) :
    prefixValue (before ++ (x, sign) :: (x, !sign) :: after) (n + 2) =
      prefixValue (before ++ after) n := by
  have hs : n + 2 - before.length = (n - before.length) + 2 := by omega
  have hnew : (before ++ (x, sign) :: (x, !sign) :: after).take (n + 2) =
      before ++ (x, sign) :: (x, !sign) :: after.take (n - before.length) := by
    rw [List.take_append, List.take_of_length_le (by omega), hs]
    rfl
  have hold : (before ++ after).take n = before ++ after.take (n - before.length) := by
    rw [List.take_append, List.take_of_length_le hn]
  rw [prefixValue, prefixValue, hnew, hold]
  exact FreeGroup.Red.exact.mpr ⟨_, FreeGroup.Red.Step.not.to_red, FreeGroup.Red.refl⟩

private theorem prefix_insert_before (before after : List (SignedLetter X)) (x : X)
    (sign : Bool) (n : ℕ) (hn : n ≤ before.length) :
    prefixValue (before ++ (x, sign) :: (x, !sign) :: after) n =
      prefixValue (before ++ after) n := by
  simp only [prefixValue, List.take_append, Nat.sub_eq_zero_of_le hn,
    List.take_zero, List.append_nil]

/-- Prefix values at surviving old positions are unchanged by cap insertion. -/
theorem prefix_insert_shift (before after : List (SignedLetter X)) (x : X)
    (sign : Bool) (n : ℕ) :
    prefixValue (before ++ (x, sign) :: (x, !sign) :: after) (shift before.length n) =
      prefixValue (before ++ after) n := by
  by_cases hn : n < before.length
  · rw [shift, ite_eq_left hn]
    exact prefix_insert_before before after x sign n (Nat.le_of_lt hn)
  · rw [shift, ite_eq_right hn]
    exact prefix_insert_after before after x sign n (by omega)

/-- The value immediately after each surviving old letter is unchanged as well. -/
theorem prefix_insert_shift_succ (before after : List (SignedLetter X)) (x : X)
    (sign : Bool) (n : ℕ) :
    prefixValue (before ++ (x, sign) :: (x, !sign) :: after) (shift before.length n + 1) =
      prefixValue (before ++ after) (n + 1) := by
  by_cases hn : n < before.length
  · rw [shift, ite_eq_left hn]
    exact prefix_insert_before before after x sign (n + 1) (by omega)
  · rw [shift, ite_eq_right hn]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      prefix_insert_after before after x sign (n + 1) (by omega)

/-- The path between the inner sides of every cap has trivial free-group value. -/
theorem arc_prefix {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    ∀ arc ∈ P.arcs, prefixValue w arc.2 = prefixValue w (arc.1 + 1) := by
  induction P with
  | empty => simp [arcs]
  | insert before after x sign old ih =>
    intro arc ha
    simp only [arcs, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨oldArc, hm, rfl⟩
    · rfl
    · change prefixValue _ (shift before.length oldArc.2) =
        prefixValue _ (shift before.length oldArc.1 + 1)
      rw [prefix_insert_shift, prefix_insert_shift_succ]
      exact ih oldArc hm

/-- Crossing an actual cap multiplies its prefix value by its actual signed label. -/
theorem edge_prefix {w : List (SignedLetter X)} (P : BoundaryPairing w) (d : Fin w.length) :
    prefixValue w (P.ribbon.edge d).val = prefixValue w d.val * letterValue w[d] := by
  obtain ⟨⟨i, sign⟩, rfl⟩ := P.position_bijective.surjective d
  have hp := P.arc_prefix P.arcs[i] (List.getElem_mem i.isLt)
  have hs := prefixValue_succ w (P.position (i, false))
  have hforward : prefixValue w (P.position (i, true)).val =
      prefixValue w (P.position (i, false)).val * letterValue w[P.position (i, false)] :=
    hp.trans hs
  cases sign with
  | false => simpa only [P.ribbon_edge_position, reverseDart_apply, Bool.not_false] using hforward
  | true =>
    rw [P.ribbon_edge_position]
    change prefixValue w (P.position (i, false)).val =
      prefixValue w (P.position (i, true)).val * letterValue w[P.position (i, true)]
    have hl := P.ribbon_edge_letter (P.position (i, false))
    simp only [P.ribbon_edge_position, reverseDart_apply, Bool.not_false] at hl
    change w[P.position (i, true)] = reverseLetter w[P.position (i, false)] at hl
    rw [hl, letterValue_reverse, hforward, mul_assoc, mul_inv_cancel, mul_one]

end BoundaryPairing
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
