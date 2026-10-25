module

public import SmallPresentation.SmallCancellationBandPieces

/-! The metric hypothesis distinguishes indexed oriented augmented row words. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Augmentation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)

/-- Equality of full marker/coefficient words forces equality of their original indexed origins. -/
theorem word_injective (hmetric : MetricSmallCancellation G length rows) :
    Function.Injective (word G length rows) := by
  intro a b h
  have hl := congrArg List.length h
  simp only [word_length] at hl
  apply origin_eq_of_full_overlap G length rows hmetric a b (by omega)
  intro t ht
  have hp : 2 * t < (word G length rows a).length := by rw [word_length]; omega
  have he := List.getElem_of_eq h hp
  simp only [word, List.getElem_ofFn, entry_even] at he
  exact syllable_eq_of_tag_and_value G (congrArg (fun x ↦ x.1.1) he) (congrArg Prod.snd he)

end SmallPresentationStatements.RelativeSmallCancellation.Augmentation
