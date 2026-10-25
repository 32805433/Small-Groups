module

public import SmallPresentation.SmallCancellationGeometryRelativeMetric

/-!
# Cyclic reduction from exact augmented row readings

Nonidentity row syllables and different neighboring factor tags imply cyclic reduction of
any actual augmented ribbon carrying those indexed readings in both orientations.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
variable {length : I → ℕ} [∀ i, NeZero (length i)]
variable {rows : ∀ i, Fin (length i) → Syllable G}

/-- Nonidentity syllables remain nonidentity in every oriented cyclic reading. -/
theorem syllableAt_include_ne_one
    (hidentity : ∀ i p, (rows i p).2 ≠ 1) (a : Origin length) (t : ℕ) :
    includeSyllable G (syllableAt G length rows a t) ≠ 1 := by
  intro he
  rcases a with ⟨i, b, p⟩
  cases b <;> dsimp [syllableAt, oriented, inverseSyllable, includeSyllable] at he
  · have hh := Monoid.CoprodI.of_injective _ (he.trans (map_one _).symm)
    exact hidentity _ _ (inv_eq_one.mp hh)
  · exact hidentity _ _ (Monoid.CoprodI.of_injective _ (he.trans (map_one _).symm))

/-- The two first factor tags in every oriented cyclic reading are different. -/
theorem syllableAt_zero_tag_ne_one
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1) (a : Origin length) :
    (syllableAt G length rows a 0).1 ≠ (syllableAt G length rows a 1).1 := by
  have hc : (Fin.ofNat (length a.row) 1 : Fin (length a.row)) = 1 := rfl
  cases hf : a.forward with
  | true => simpa only [syllableAt, oriented, hf, Bool.true_eq, ite_true, hc, Fin.ofNat_zero, add_zero] using hreduced a.row a.position
  | false =>
    have hh := hreduced a.row (-(a.position + 1))
    have hp : -(a.position + 1) + 1 = -a.position := by simp
    rw [hp] at hh
    simpa only [syllableAt, oriented, inverseSyllable, hf, Bool.false_eq_true, ite_false, hc, Fin.ofNat_zero, add_zero] using Ne.symm hh

namespace Geometry.AugmentedReadings

variable {Y : Type*} {P : RibbonMap Y}
variable {L : RibbonLabelling P A (Monoid.CoprodI G)}
variable (Q : AugmentedReadings G length rows P L)

/-- A positive marker is followed by the nonidentity syllable coefficient it represents. -/
theorem positive_corner_ne_one (Q : AugmentedReadings G length rows P L)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1) (y : Y) (hy : (L.arc y).2 = true) :
    L.corner y ≠ 1 := by
  have hh := OppositeBand.forward_reading G length rows L y (Q.origin y)
    (Q.forward y hy) 0 (by have := Fin.pos (Q.origin y).position; omega)
  have hc := congrArg Prod.snd hh
  simp only [Function.iterate_zero_apply] at hc
  rw [hc]
  exact syllableAt_include_ne_one hidentity (Q.origin y) 0

/-- Negative markers carry identity corners, as follows from the full forward reading
at their preceding positive marker. -/
theorem negative_corner_eq_one (Q : AugmentedReadings G length rows P L) (y : Y) (hy : (L.arc y).2 = false) : L.corner y = 1 := by
  have ha := Q.alternating (P.rotation.symm y)
  have hp : (L.arc (P.rotation.symm y)).2 = true := by
    cases hs : (L.arc (P.rotation.symm y)).2 <;> simp_all
  have hh := OppositeBand.forward_reading G length rows L (P.rotation.symm y)
    (Q.origin (P.rotation.symm y)) (Q.forward _ hp) 1
    (by have := Fin.pos (Q.origin (P.rotation.symm y)).position; omega)
  have hc := congrArg Prod.snd hh
  simpa [Augmentation.entry] using hc

/-- Every actual augmented vertex is cyclically reduced when the rows are cyclically
reduced, have nonidentity syllables, and have at least two syllables. -/
theorem cyclicallyReduced (Q : AugmentedReadings G length rows P L)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 2 ≤ length i) : L.CyclicallyReduced := by
  intro y hc he
  have hy : (L.arc y).2 = false := by
    cases hs : (L.arc y).2 with
    | false => rfl
    | true => exact False.elim (Q.positive_corner_ne_one hidentity y hs hc)
  let p := P.rotation.symm y
  have hp : (L.arc p).2 = true := by
    have hh := Q.alternating p
    simpa [p, hy] using hh.symm
  have h0 := OppositeBand.forward_reading G length rows L p (Q.origin p)
    (Q.forward p hp) 1 (by have := hlength (Q.origin p).row; omega)
  have h1 := OppositeBand.forward_reading G length rows L p (Q.origin p)
    (Q.forward p hp) 2 (by have := hlength (Q.origin p).row; omega)
  have ht0 := congrArg (fun x ↦ x.1.1) h0
  have ht1 := congrArg (fun x ↦ x.1.1) h1
  have hn := syllableAt_zero_tag_ne_one hreduced (Q.origin p)
  apply hn
  have he' := congrArg Prod.fst he
  simp [p, Augmentation.entry, Function.iterate_succ_apply'] at ht0 ht1
  exact ht0.symm.trans (he'.symm.trans ht1)

end Geometry.AugmentedReadings
end SmallPresentationStatements.RelativeSmallCancellation
