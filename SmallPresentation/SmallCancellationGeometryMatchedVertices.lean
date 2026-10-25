module

public import SmallPresentation.SmallCancellationDipolePairOrbits
public import SmallPresentation.SmallCancellationGeometryAugmentedLocal
public import SmallPresentation.SmallCancellationAugmentedWordInjectivity

/-! Matched opposite readings belong to distinct actual vertices. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

open PermutationCycles AugmentedOccurrence

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    {D : Type*} [Finite D] (P : RibbonMap D)
    (L : RibbonLabelling P A (Monoid.CoprodI G))

namespace ReadingOrbit

variable (a : D) (o : Origin length)
    (hword : L.vertexWord a = Augmentation.word G length rows o)

def start : Fin (length o.row) := bif o.forward then o.position else o.position - 1

@[simp] theorem positiveOrigin_start :
    positiveOrigin length o.row o.forward (start length o) = o := by
  rcases o with ⟨i, sign, k⟩
  cases sign <;> simp [start, positiveOrigin]

include hword in
omit [Finite D] in
theorem period : Function.minimalPeriod P.rotation a = 2 * length o.row := by
  simpa [RibbonLabelling.vertexWord] using congrArg List.length hword

noncomputable def coordinates : Darts length (fun _ : Unit ↦ o.row) → D :=
  fun d ↦ (doubleOrbit P.rotation a (period G length rows P L a o hword)
    (d.2.1 - start length o, d.2.2)).val

include hword in
theorem coordinates_injective : Function.Injective (coordinates G length rows P L a o hword) := by
  rintro ⟨⟨⟩, k, b⟩ ⟨⟨⟩, l, c⟩ h
  have hh := (doubleOrbit P.rotation a (period G length rows P L a o hword)).injective
    (Subtype.ext h)
  have hk : k = l := (sub_left_inj).mp (congrArg Prod.fst hh)
  have hb : b = c := congrArg Prod.snd hh
  subst l
  subst c
  rfl

include hword in
theorem coordinates_rotation (d : Darts length (fun _ : Unit ↦ o.row)) :
    coordinates G length rows P L a o hword (rotation length (fun _ : Unit ↦ o.row) d) =
      P.rotation (coordinates G length rows P L a o hword d) := by
  rcases d with ⟨⟨⟩, k, b⟩
  have hh := doubleOrbit_rotation P.rotation a (period G length rows P L a o hword)
    (k - start length o, b)
  cases b
  · exact hh
  · change (doubleOrbit P.rotation a _ (k + 1 - start length o, false)).val = _
    convert hh using 1
    · congr 3
      rw [finRotate_apply]
      abel
    · rfl

include hword in
theorem coordinates_entry (d : Darts length (fun _ : Unit ↦ o.row)) :
    (L.arc (coordinates G length rows P L a o hword d),
      L.corner (coordinates G length rows P L a o hword d)) =
      (arc length G rows (fun _ : Unit ↦ o.row) (fun _ ↦ o.forward) d,
       corner length G rows (fun _ : Unit ↦ o.row) (fun _ ↦ o.forward) d) := by
  rcases d with ⟨⟨⟩, k, b⟩
  let j := k - start length o
  have hreading := OppositeBand.forward_reading G length rows L a o hword
    (2 * j.val + if b then 1 else 0) (by have hj : j.val < length o.row := j.isLt; cases b <;> simp only [Bool.false_eq_true, reduceIte] <;> omega)
  have hsyll : syllableAt G length rows o j.val =
      literalSyllable length G rows o.row o.forward k := by
    have hh := positive_syllableAt length G rows o.row o.forward (start length o) j.val
    have hj : start length o + Fin.ofNat (length o.row) j.val = k := by
      change start length o + Fin.ofNat (length o.row) (k - start length o).val = k
      simp
    rw [positiveOrigin_start, hj] at hh
    exact hh
  change (L.arc ((doubleOrbit P.rotation a _ (j,b)).val),
    L.corner ((doubleOrbit P.rotation a _ (j,b)).val)) = _
  rw [doubleOrbit_val]
  cases b
  · simpa only [Bool.false_eq_true, reduceIte, Nat.add_zero, Augmentation.entry_even,
      hsyll, arc, corner, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.cond_false, Bool.cond_true] using hreading
  · simpa only [reduceIte, Augmentation.entry_odd, hsyll, arc, corner, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.cond_false, Bool.cond_true] using hreading

include hword in
theorem coordinates_surjective (b : D) (hb : P.rotation.SameCycle a b) :
    ∃ d, coordinates G length rows P L a o hword d = b := by
  let z := (doubleOrbit P.rotation a (period G length rows P L a o hword)).symm ⟨b,hb⟩
  refine ⟨⟨(), z.1 + start length o, z.2⟩, ?_⟩
  change (doubleOrbit P.rotation a _ (z.1 + start length o - start length o,z.2)).val = b
  rw [add_sub_cancel_right]
  exact congrArg Subtype.val ((doubleOrbit P.rotation a _).apply_symm_apply ⟨b,hb⟩)

end ReadingOrbit

/-- A complete row and an inverse complete reading with the same indexed origin cannot
occur at one actual vertex under the metric small-cancellation hypothesis. -/
theorem matched_readings_distinct_vertices
    (hmetric : MetricSmallCancellation G length rows) (a b : D) (o : Origin length)
    (hforward : L.vertexWord a = Augmentation.word G length rows o)
    (hbackward : L.reverseVertexWord b = Augmentation.word G length rows o)
    (hnegative : (L.arc b).2 = false) : ¬P.rotation.SameCycle a b := by
  intro hab
  obtain ⟨⟨⟨⟩, k, phase⟩, hk⟩ :=
    ReadingOrbit.coordinates_surjective G length rows P L a o hforward b hab
  have hentry := ReadingOrbit.coordinates_entry G length rows P L a o hforward ⟨(),k,phase⟩
  have hphase := congrArg (fun x ↦ x.1.2) hentry
  rw [hk, hnegative] at hphase
  have htrue : phase = true := by
    change false = !phase at hphase
    cases phase
    · cases hphase
    · rfl
  subst phase
  have hw := backward_of_coordinates length G rows (fun _ : Unit ↦ o.row)
    (fun _ ↦ o.forward) L (ReadingOrbit.coordinates G length rows P L a o hforward)
    (ReadingOrbit.coordinates_injective G length rows P L a o hforward)
    (ReadingOrbit.coordinates_rotation G length rows P L a o hforward)
    (fun d ↦ congrArg Prod.fst (ReadingOrbit.coordinates_entry G length rows P L a o hforward d))
    (fun d ↦ congrArg Prod.snd (ReadingOrbit.coordinates_entry G length rows P L a o hforward d))
    () k
  rw [hk, hbackward] at hw
  have ho := Augmentation.word_injective G length rows hmetric hw
  have hs := congrArg Origin.forward ho
  change o.forward = !o.forward at hs
  cases ht : o.forward <;> simp only [ht, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false] at hs

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
