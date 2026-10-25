module

public import SmallPresentation.SmallCancellationGeometrySprayBoundary
public import SmallPresentation.SmallCancellationGeometrySprayPotentials
public import SmallPresentation.SmallCancellationGeometryIdentityBasedPaths

/-!
# Boundary-prefix potentials on the actual conjugator corridors

The quotient kills each signed relator row. Consequently opposite corridor sides have the
same prefix-potential law as cap edges. This combines with the checked first-return band
formula to control the actual based paths at the endpoints of relator-ribbon edges.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {X : Type*}

theorem prefixValue_append_left (u v : List (SignedLetter X)) (n : ℕ) (hn : n ≤ u.length) :
    prefixValue (u ++ v) n = prefixValue u n := by
  simp only [prefixValue, List.take_append, Nat.sub_eq_zero_of_le hn,
    List.take_zero, List.append_nil]

theorem prefixValue_append_right (u v : List (SignedLetter X)) (n : ℕ) :
    prefixValue (u ++ v) (u.length + n) = FreeGroup.mk u * prefixValue v n := by
  rw [prefixValue, List.take_append, List.take_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact (FreeGroup.mul_mk).symm

theorem prefixValue_invRev (u : List (SignedLetter X)) (n : ℕ) :
    FreeGroup.mk u * prefixValue (FreeGroup.invRev u) n =
      prefixValue u (u.length - n) := by
  have hr : (FreeGroup.invRev u).take n = FreeGroup.invRev (u.drop (u.length - n)) := by
    simp only [FreeGroup.invRev, List.take_reverse, List.length_map, List.map_drop]
  rw [prefixValue, hr, ← FreeGroup.inv_mk]
  have hu : FreeGroup.mk u = prefixValue u (u.length - n) *
      FreeGroup.mk (u.drop (u.length - n)) := by
    rw [prefixValue, FreeGroup.mul_mk, List.take_append_drop]
  rw [hu, mul_assoc, mul_inv_cancel, mul_one]

namespace IdentityBoundary

open RelationCoordinates

variable {X I Q : Type} [Group Q] (paths : WordSection X)
    (rows : I → List (SignedLetter X)) (q : FreeGroup X →* Q)
    (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1)

include hkill

theorem orientedWord_quotient (i : I) (sign : Bool) :
    q (FreeGroup.mk (orientedWord (rows i) sign)) = 1 := by
  cases sign <;> simp [orientedWord, ← FreeGroup.inv_mk, hkill]

theorem block_quotient (a : Peiffer.Occurrence (FreeGroup X) I) :
    q (FreeGroup.mk (block paths rows a)) = 1 := by
  rw [block_evaluates]
  exact Peiffer.quotient_term _ q hkill a

/-- Potential at an actual ordered block-boundary dart. -/
def blockPotential (a : Peiffer.Occurrence (FreeGroup X) I) (d : BlockDart paths rows a) : Q :=
  q (prefixValue (block paths rows a) (blockCoordinates paths rows a d).val)

omit hkill in
theorem blockPotential_out (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : Fin (paths.word a.1.1).length) :
    blockPotential paths rows q a (.inl d) = q (prefixValue (paths.word a.1.1) d.val) := by
  change q (prefixValue (block paths rows a) d.val) = _
  rw [block, List.append_assoc,
    prefixValue_append_left _ _ _ (Nat.le_of_lt d.isLt)]

theorem blockPotential_back (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : Fin (paths.word a.1.1).length) :
    blockPotential paths rows q a (.inr (.inr d)) =
      q (prefixValue (paths.word a.1.1) ((paths.word a.1.1).length - d.val)) := by
  change q (prefixValue (block paths rows a) ((paths.word a.1.1).length +
    ((orientedWord (rows a.1.2) a.2).length + d.val))) = _
  rw [block, List.append_assoc, prefixValue_append_right, prefixValue_append_right,
    map_mul, map_mul, orientedWord_quotient rows q hkill, one_mul, ← map_mul,
    prefixValue_invRev]

omit hkill in
/-- The path at a relator corner consists of the conjugator and its signed row prefix. -/
theorem blockPotential_row (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : Fin (orientedWord (rows a.1.2) a.2).length) :
    blockPotential paths rows q a (.inr (.inl d)) =
      q a.1.1 * q (prefixValue (orientedWord (rows a.1.2) a.2) d.val) := by
  change q (prefixValue (block paths rows a) ((paths.word a.1.1).length + d.val)) = _
  rw [block, List.append_assoc, prefixValue_append_right,
    prefixValue_append_left _ _ _ (Nat.le_of_lt d.isLt), map_mul, paths.evaluates]

/-- Every actual non-fixed corridor side obeys the quotient path-potential equation. -/
theorem corridorReverse_potential (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : BlockDart paths rows a) (hd : corridorReverse paths rows a d ≠ d) :
    blockPotential paths rows q a (corridorReverse paths rows a d) =
      blockPotential paths rows q a d * q (letterValue (blockRead paths rows a d)) := by
  rcases d with d | (d | d)
  · change blockPotential paths rows q a (.inr (.inr d.rev)) = _
    rw [blockPotential_back paths rows q hkill, blockPotential_out]
    have hn : (paths.word a.1.1).length - d.rev.val = d.val + 1 := by
      change (paths.word a.1.1).length - ((paths.word a.1.1).length - (d.val + 1)) = _
      omega
    rw [hn, prefixValue_succ, map_mul]
    rfl
  · exact (hd rfl).elim
  · change blockPotential paths rows q a (.inl d.rev) = _
    rw [blockPotential_out, blockPotential_back paths rows q hkill]
    have hh := prefixValue_succ (paths.word a.1.1) d.rev
    have hn : d.rev.val + 1 = (paths.word a.1.1).length - d.val := by
      change (paths.word a.1.1).length - (d.val + 1) + 1 = _
      omega
    rw [hn] at hh
    have hl := invRev_letter (paths.word a.1.1) d.rev
    simp only [Fin.rev_rev] at hl
    change q (prefixValue _ d.rev.val) = _ * q (letterValue
      ((FreeGroup.invRev (paths.word a.1.1))[Fin.cast FreeGroup.invRev_length.symm d]))
    rw [hl, letterValue_reverse, hh, map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one]

end IdentityBoundary
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
