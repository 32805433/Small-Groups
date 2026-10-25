module

public import SmallPresentation.PermutationCyclePartition
public import SmallPresentation.PermutationCycleCounts

/-!
# Cutting an explicitly ordered vertex cycle into two intervals

Switching the two incoming arrows at the beginnings of two nonempty cyclic intervals
splits their combined rotation into exactly their two separate rotations. The proof
intertwines the actual finite permutations and yields an equivalence of cycle quotients.
This is a local vertex-cut calculation; it makes no connectedness or planarity claim.
-/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

/-- The two marked interval beginnings on a finite cyclic boundary. -/
def intervalStartLeft (m n : ℕ) : Fin ((m + 1) + (n + 1)) :=
  finSumFinEquiv (.inl 0 : Fin (m + 1) ⊕ Fin (n + 1))

def intervalStartRight (m n : ℕ) : Fin ((m + 1) + (n + 1)) :=
  finSumFinEquiv (.inr 0 : Fin (m + 1) ⊕ Fin (n + 1))

/-- Switch the incoming arrows at the two cut points of an ordered boundary cycle. -/
def intervalSplit (m n : ℕ) : Equiv.Perm (Fin ((m + 1) + (n + 1))) :=
  (finRotate _).trans (Equiv.swap (intervalStartLeft m n) (intervalStartRight m n))

private theorem rotate_val {N : ℕ} (_hN : 0 < N) (i : Fin N) :
    (finRotate N i).val = (i.val + 1) % N := by
  rw [finRotate_apply]
  change (i.val + (1 % N)) % N = (i.val + 1) % N
  exact Nat.add_mod_mod _ _ _

/-- Literal ordered interval coordinates intertwine the cut permutation with two rotations. -/
theorem intervalSplit_intertwines (m n : ℕ) (d : Fin (m + 1) ⊕ Fin (n + 1)) :
    finSumFinEquiv (Equiv.sumCongr (finRotate (m + 1)) (finRotate (n + 1)) d) =
      intervalSplit m n (finSumFinEquiv d) := by
  have htotal : 0 < (m + 1) + (n + 1) := by omega
  rcases d with d | d
  · by_cases hd : d.val = m
    · have he : finRotate ((m + 1) + (n + 1)) (finSumFinEquiv (.inl d)) =
          intervalStartRight m n := by
        apply Fin.ext
        rw [rotate_val htotal]
        change (d.val + 1) % ((m + 1) + (n + 1)) = m + 1
        rw [hd, Nat.mod_eq_of_lt (by omega)]
      change finSumFinEquiv (.inl (finRotate (m + 1) d)) =
        Equiv.swap _ _ (finRotate _ (finSumFinEquiv (.inl d)))
      rw [he, Equiv.swap_apply_right]
      apply Fin.ext
      change (finRotate (m + 1) d).val = 0
      rw [rotate_val (by omega), hd, Nat.mod_self]
    · have hrot : (finRotate ((m + 1) + (n + 1)) (finSumFinEquiv (.inl d))).val = d.val + 1 := by
        rw [rotate_val htotal]
        change (d.val + 1) % ((m + 1) + (n + 1)) = _
        rw [Nat.mod_eq_of_lt (by omega)]
      change finSumFinEquiv (.inl (finRotate (m + 1) d)) = Equiv.swap _ _ _
      rw [Equiv.swap_apply_of_ne_of_ne]
      · apply Fin.ext
        change (finRotate (m + 1) d).val = _
        rw [rotate_val (by omega), hrot, Nat.mod_eq_of_lt (by omega)]
      · intro he
        have hv := congrArg Fin.val he
        change _ = 0 at hv
        rw [hrot] at hv
        omega
      · intro he
        have hv := congrArg Fin.val he
        change _ = m + 1 at hv
        rw [hrot] at hv
        omega
  · by_cases hd : d.val = n
    · have he : finRotate ((m + 1) + (n + 1)) (finSumFinEquiv (.inr d)) =
          intervalStartLeft m n := by
        apply Fin.ext
        rw [rotate_val htotal]
        change (m + 1 + d.val + 1) % ((m + 1) + (n + 1)) = 0
        rw [hd, show m + 1 + n + 1 = (m + 1) + (n + 1) by omega, Nat.mod_self]
      change finSumFinEquiv (.inr (finRotate (n + 1) d)) =
        Equiv.swap _ _ (finRotate _ (finSumFinEquiv (.inr d)))
      rw [he, Equiv.swap_apply_left]
      apply Fin.ext
      change m + 1 + (finRotate (n + 1) d).val = m + 1
      rw [rotate_val (by omega), hd, Nat.mod_self, Nat.add_zero]
    · have hrot : (finRotate ((m + 1) + (n + 1)) (finSumFinEquiv (.inr d))).val =
          m + 1 + d.val + 1 := by
        rw [rotate_val htotal]
        change (m + 1 + d.val + 1) % ((m + 1) + (n + 1)) = _
        rw [Nat.mod_eq_of_lt (by omega)]
      change finSumFinEquiv (.inr (finRotate (n + 1) d)) = Equiv.swap _ _ _
      rw [Equiv.swap_apply_of_ne_of_ne]
      · apply Fin.ext
        change m + 1 + (finRotate (n + 1) d).val = _
        rw [rotate_val (by omega), hrot, Nat.mod_eq_of_lt (by omega)]
        omega
      · intro he
        have hv := congrArg Fin.val he
        change _ = 0 at hv
        rw [hrot] at hv
        omega
      · intro he
        have hv := congrArg Fin.val he
        change _ = m + 1 at hv
        rw [hrot] at hv
        omega

/-- Cutting the actual cyclic interval gives the disjoint union of its two cycle sets. -/
def intervalSplitCyclesEquiv (m n : ℕ) :
    Cycles (intervalSplit m n) ≃ Cycles (finRotate (m + 1)) ⊕ Cycles (finRotate (n + 1)) :=
  (conjugateEquiv _ _ finSumFinEquiv (intervalSplit_intertwines m n)).symm.trans
    (sumCyclesEquiv _ _)

/-- A cut at two distinct interval beginnings produces exactly two actual vertex cycles. -/
theorem card_intervalSplitCycles (m n : ℕ) [Fintype (Cycles (intervalSplit m n))] :
    Fintype.card (Cycles (intervalSplit m n)) = 2 := by
  classical
  let := Fintype.ofFinite (Cycles (finRotate (m + 1)))
  let := Fintype.ofFinite (Cycles (finRotate (n + 1)))
  have h := Fintype.card_congr (intervalSplitCyclesEquiv m n)
  rw [Fintype.card_sum, card_finRotateCycles (m + 1) (by omega),
    card_finRotateCycles (n + 1) (by omega)] at h
  exact h

end SmallPresentationStatements.PermutationCycles
