module

public import SmallPresentation.UniversalGroup.Coding.Thue.PriorityForward

/-
Ported from `GroupUndecidability/Thue/Matiyasevich/PriorityForward.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.Matiyasevich.Compression
public import SmallPresentation.AdianRabin.Thue.Matiyasevich.RowSelection

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Compression

open Priority Priority.RowSelection Precompression

variable {n r : ℕ}

theorem width_gt_two (F E : Fin r → List (Fin n)) :
    2 < Precompression.leftWidth F E ∧
      2 < Precompression.rightWidth F E := by
  have hp := Padding.p_pos F E
  have hmul (k : ℕ) (hk : 0 < k) : 2 < k * (n + 5) := by
    calc
      2 < n + 5 := by omega
      _ = 1 * (n + 5) := by simp
      _ ≤ k * (n + 5) := Nat.mul_le_mul_right _ hk
  constructor
  · exact hmul _ hp
  · simpa [Precompression.rightWidth, Padding.q] using
      hmul (Padding.p F E + 1) (Nat.succ_pos _)

theorem longShape_of_prefix_and_last
    {W : List Priority.A₂} {run : ℕ}
    (hprefix : ∃ tail, W = List.replicate run a ++ tail)
    (hlength : run < W.length)
    (hlast : ∃ init, W = init ++ [b]) : LongShape run W := by
  obtain ⟨tail, htail⟩ := hprefix
  have htail_ne : tail ≠ [] := by
    intro hempty
    subst tail
    rw [htail] at hlength
    simp at hlength
  have hlastW : W.getLast? = some b := by
    obtain ⟨init, rfl⟩ := hlast
    simp
  have hlastTail : tail.getLast? = some b := by
    calc
      tail.getLast? = (List.replicate run a ++ tail).getLast? :=
        (List.getLast?_append_of_ne_nil _ htail_ne).symm
      _ = W.getLast? := congrArg List.getLast? htail.symm
      _ = some b := hlastW
  obtain ⟨middle, hmiddle⟩ := List.getLast?_eq_some_iff.mp hlastTail
  exact ⟨middle, by rw [htail, hmiddle, List.append_assoc]⟩

theorem transposedShape
    (rows : Fin (t n r) → List (Fin 2)) (width : ℕ)
    (hwidth : 2 < width)
    (hlength : ∀ i, (rows i).length = width)
    (hstarts : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail)
    (hends : ∀ i, ∃ init, rows i = init ++ [(1 : Fin 2)]) :
    LongShape (2 * t n r) (liftBinary (transpose width rows)) := by
  apply longShape_of_prefix_and_last
  · obtain ⟨tail, htail⟩ := transpose_starts_two_columns rows
      (Nat.le_of_lt hwidth) hstarts
    refine ⟨liftBinary tail, ?_⟩
    rw [htail, liftBinary_append]
    simp [liftBinary, liftBit, a]
  · simp only [liftBinary, List.length_map, transpose_length]
    exact Nat.mul_lt_mul_of_pos_right hwidth (t_pos n r)
  · exact liftBinary_transpose_ends_b rows (t_pos n r) (by omega)
      hlength hends

/-- The transposed left long word begins with `2t` copies of `a` and ends
with `b`, exactly as required in the page-50 counting argument. -/
theorem leftShape (F E : Fin r → List (Fin n)) :
    LongShape (2 * t n r) (leftLong F E) := by
  simpa [leftLong] using transposedShape (paddedLeftRows F E)
    (Precompression.leftWidth F E) (width_gt_two F E).1
    (paddedLeftRows_length F E) (paddedLeftRows_starts_aa F E)
    (paddedLeftRows_ends_b F E)

/-- The analogous shape theorem for the right long word. -/
theorem rightShape (F E : Fin r → List (Fin n)) :
    LongShape (2 * t n r) (rightLong F E) := by
  simpa [rightLong] using transposedShape (paddedRightRows F E)
    (Precompression.rightWidth F E) (width_gt_two F E).2
    (paddedRightRows_length F E) (paddedRightRows_starts_aa F E)
    (paddedRightRows_ends_b F E)

/-- The fixed compression uses the canonical compiler's zero terminal marker. -/
theorem encodeWith_zero (u : ℕ) (W : List (Fin 2)) :
    PriorityCompiler.encodeWith u 0 W = encode u W := by
  simp [PriorityCompiler.encodeWith, encode, liftBinary, liftBit, a, List.append_assoc]

/-- One directed binary row replacement is simulated by the four
housekeeping relations, one use of the long relation, and the housekeeping
relations again. -/
theorem simulate_row (F E : Fin r → List (Fin n))
    (j : Fin (t n r)) (left right : List (Fin 2)) :
    ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (encode (u n r) (left ++ paddedLeftRows F E j ++ right))
      (encode (u n r) (left ++ paddedRightRows F E j ++ right)) := by
  simpa only [encodeWith_zero, leftLong, rightLong, t, u, powerCount] using
    PriorityCompiler.simulate_row (u n r) (Precompression.leftWidth F E)
      (Precompression.rightWidth F E) 0 (paddedLeftRows F E) (paddedRightRows F E)
      (paddedLeftRows_length F E) (paddedRightRows_length F E) j left right

/-- Forward half of Matiyasevich's priority-compression equivalence: every
binary rewrite, in arbitrary two-sided context, is simulated by the
five-relation system on `{a,b,e}`. -/
theorem simulate_binary (F E : Fin r → List (Fin n))
    {X Y : List (Fin 2)} (h : ThueEq (binarySystem F E) X Y) :
    ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (encode (u n r) X) (encode (u n r) Y) := by
  simpa only [encodeWith_zero, leftLong, rightLong, t, u, powerCount] using
    PriorityCompiler.simulate_binary (u n r) (Precompression.leftWidth F E)
      (Precompression.rightWidth F E) 0 (paddedLeftRows F E) (paddedRightRows F E)
      (paddedLeftRows_length F E) (paddedRightRows_length F E) h

end Compression
end Matiyasevich1993
end Thue
end UniversalGroup
