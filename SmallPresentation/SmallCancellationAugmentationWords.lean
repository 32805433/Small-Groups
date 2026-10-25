module

public import SmallPresentation.SmallCancellationAugmentationQuotient

/-!
# Word coordinates for augmentation and general metric consequences

The hypotheses are the indexed metric piece condition, with no fixed relator lengths. In
particular the metric condition itself forces length at least seven, because a syllable and its
inverse give distinct length-one oriented origins. The augmentation formulas identify the literal
conjugated syllable product with the image under the ambient automorphism.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]
variable (rows : ∀ i, Fin (length i) → Syllable G)

/-- Every row has a length-one semi-initial piece from the opposite orientation. -/
theorem opposite_orientation_piece_one (i : I) :
    Piece G length rows ⟨i, true, 0⟩ 1 := by
  refine ⟨⟨i, false, 0⟩, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun a : Origin length ↦ a.forward) h
    contradiction
  · exact Fin.pos (0 : Fin (length i))
  · exact Fin.pos (0 : Fin (length i))
  · intro t ht
    omega
  · have hn : -(0 : Fin (length i)) = 0 := by
      apply Fin.ext
      simp [Fin.neg_def]
    simp [syllableAt, oriented, inverseSyllable, hn]

/-- The general metric hypothesis implies the length cutoff needed for generalized presentations.
This is a consequence, not an additional hypothesis on the input. -/
theorem seven_le_length_of_metric
    (hmetric : MetricSmallCancellation G length rows) (i : I) : 7 ≤ length i := by
  have h := hmetric ⟨i, true, 0⟩ 1 (opposite_orientation_piece_one G length rows i)
  change 6 * 1 < length i at h
  omega

/-- Once a semi-initial match is too long to be a piece, the oriented origins coincide. -/
theorem origin_eq_of_long_semiInitial
    (hmetric : MetricSmallCancellation G length rows) (a b : Origin length) (m : ℕ)
    (hmatch : SemiInitial G length rows a b m) (hlong : length a.row ≤ 6 * m) : a = b := by
  by_contra hne
  have hp : Piece G length rows a m := ⟨b, Ne.symm hne, hmatch⟩
  have h := hmetric a m hp
  omega

/-- Full cyclic sequences distinguish all indexed oriented origins under the metric hypothesis. -/
theorem cyclic_sequence_injective
    (hmetric : MetricSmallCancellation G length rows) :
    Function.Injective (fun a : Origin length ↦ syllableAt G length rows a) := by
  intro a b h
  rcases le_total (length a.row) (length b.row) with hab | hba
  · exact origin_eq_of_full_overlap G length rows hmetric a b hab
      (fun t _ ↦ congrFun h t)
  · exact (origin_eq_of_full_overlap G length rows hmetric b a hba
      (fun t _ ↦ (congrFun h t).symm)).symm

/-- An oriented cyclic row cannot agree with an oppositely oriented cyclic row. -/
theorem cyclic_sequence_ne_of_orientation_ne
    (hmetric : MetricSmallCancellation G length rows) (a b : Origin length)
    (hdir : a.forward ≠ b.forward) :
    syllableAt G length rows a ≠ syllableAt G length rows b := by
  intro h
  exact hdir (congrArg Origin.forward (cyclic_sequence_injective G length rows hmetric h))

namespace Augmentation

omit [∀ i, NeZero (length i)] in
/-- Augmentation of a literal indexed row is its product of conjugated syllables. -/
theorem augment_relatorValue (i : I) :
    augment G (relatorValue G length rows i) =
      (List.ofFn fun p : Fin (length i) ↦
        letter G (rows i p).1 * factor G (rows i p).1 (rows i p).2 *
          (letter G (rows i p).1)⁻¹).prod := by
  change conjugatedBase G false
    ((List.ofFn fun p ↦ includeSyllable G (rows i p)).prod) = _
  rw [map_list_prod, List.map_ofFn]
  congr 1

/-- Specialization of the quotient isomorphism to the exact row family used by the metric API. -/
def rowQuotientEquiv :
    Monoid.Coprod (Quotient G length rows) (FreeGroup A) ≃*
      AugmentedQuotient G (relatorValue G length rows) :=
  quotientEquiv G (relatorValue G length rows)

omit [∀ i, NeZero (length i)] in
/-- Coefficient injection implies injectivity of the exact factor maps used by the metric API. -/
theorem row_factor_injective_of_coefficient_injective
    (h : Function.Injective (coefficient G (relatorValue G length rows))) (a : A) :
    Function.Injective (factorMap G length rows a) :=
  factor_injective_of_coefficient_injective G (relatorValue G length rows) h a

end Augmentation
end SmallPresentationStatements.RelativeSmallCancellation
