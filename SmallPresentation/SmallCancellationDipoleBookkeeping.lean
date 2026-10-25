module

public import SmallPresentation.SmallCancellationDipoleDeletion

/-!
# Occurrence count and additive conservation under dipole deletion

The deleted picture retains precisely the original indices other than the two named rows.
This gives a strict finite induction measure and conservation of every additive contribution
whose values at those two indices cancel.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RowDeletion

variable {O : Type} (i j : O) (hij : i ≠ j)

def occurrenceEmbed : Remaining i j ⊕ Bool → O
  | .inl o => o.val
  | .inr false => i
  | .inr true => j

include hij in
theorem occurrenceEmbed_bijective : Function.Bijective (occurrenceEmbed i j) := by
  constructor
  · intro a b hab
    rcases a with ⟨a, ha⟩ | (_ | _) <;> rcases b with ⟨b, hb⟩ | (_ | _)
    · exact congrArg Sum.inl (Subtype.ext hab)
    · exact (ha.1 hab).elim
    · exact (ha.2 hab).elim
    · exact (hb.1 hab.symm).elim
    · rfl
    · exact (hij hab).elim
    · exact (hb.2 hab.symm).elim
    · exact (hij hab.symm).elim
    · rfl
  · intro o
    by_cases hi : o = i
    · exact ⟨.inr false, hi.symm⟩
    by_cases hj : o = j
    · exact ⟨.inr true, hj.symm⟩
    exact ⟨.inl ⟨o, hi, hj⟩, rfl⟩

noncomputable def occurrenceCoordinates : Remaining i j ⊕ Bool ≃ O :=
  Equiv.ofBijective _ (occurrenceEmbed_bijective i j hij)

variable [Fintype O]
include hij

theorem card_remaining [Fintype (Remaining i j)] :
    Fintype.card O = Fintype.card (Remaining i j) + 2 := by
  have hh := Fintype.card_congr (occurrenceCoordinates i j hij)
  simpa using hh.symm

theorem card_remaining_lt [Fintype (Remaining i j)] :
    Fintype.card (Remaining i j) < Fintype.card O := by
  rw [card_remaining i j hij]
  omega

theorem sum_decomposition [Fintype (Remaining i j)] {A : Type} [AddCommMonoid A] (f : O → A) :
    ∑ o, f o = (∑ o : Remaining i j, f o.val) + (f i + f j) := by
  have hh := (occurrenceCoordinates i j hij).sum_comp f
  simpa [occurrenceCoordinates, occurrenceEmbed, Fintype.sum_sum_type,
    Fintype.sum_bool, add_comm] using hh.symm

theorem sum_preserved [Fintype (Remaining i j)] {A : Type} [AddCommMonoid A]
    (f : O → A) (hcancel : f i + f j = 0) :
    ∑ o, f o = ∑ o : Remaining i j, f o.val := by
  rw [sum_decomposition i j hij, hcancel, add_zero]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RowDeletion
