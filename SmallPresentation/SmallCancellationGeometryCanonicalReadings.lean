module

public import SmallPresentation.SmallCancellationGeometryCanonicalFactor
public import SmallPresentation.SmallCancellationGeometryAugmentedLocal
public import SmallPresentation.SmallCancellationGeometryRelativeExtractionReadings

/-! Literal coordinates for the new occurrences of a canonical old/new identity picture. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology
open AugmentedOccurrence

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)

omit [∀ a, Group (G a)] [∀ i, NeZero (length i)] in
theorem oriented_newWord_length (i : I) (sign : Bool) :
    (orientedWord (newWord G length rows i) sign).length = length i := by
  simp [newWord]

omit [∀ a, Group (G a)] [∀ i, NeZero (length i)] in
theorem oriented_newWord_read (i : I) (sign : Bool) (k : Fin (length i)) :
    (orientedWord (newWord G length rows i) sign)[k.val]'(by rw [oriented_newWord_length]; exact k.isLt) =
      bif sign then (rows i k, true) else (rows i k.rev, false) := by
  cases sign <;> simp [orientedWord, newWord, FreeGroup.invRev]
  congr 1
  apply Fin.ext
  simp [Fin.val_rev, Nat.sub_sub, Nat.add_comm]

variable (paths : WordSection (Syllable G))
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1)

/-- The original index identifies old vertices even when factor words have empty boundaries. -/
def oldIncidence (d : DiscDarts (words G length rows) s × Bool) : Prop :=
  ∃ r, s[discOccurrence (words G length rows) s d.1].1.2 = Sum.inl r

omit [∀ i, NeZero (length i)] in
theorem oldIncidence_invariant (d : DiscDarts (words G length rows) s × Bool) :
    oldIncidence G length rows s ((ordinary G length rows paths s hs).augmented.rotation d) ↔
      oldIncidence G length rows s d := by
  rcases d with ⟨d, b⟩
  cases b
  · rfl
  · change (∃ r, s[discOccurrence (words G length rows) s
        (discRotation (words G length rows) s d)].1.2 = Sum.inl r) ↔ _
    simp only [discOccurrence_rotation, oldIncidence]

omit [∀ i, NeZero (length i)] in
theorem new_occurrence_length (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j) :
    (orientedWord (words G length rows s[i].1.2) s[i].2).length = length j := by
  rw [hi]
  exact oriented_newWord_length G length rows j s[i].2

/-- Every old incidence of the actual initial identity belongs to its original factor disc. -/
noncomputable def oldDiscSystem : OldDiscSystem (augmentedData G length rows paths s hs).labelling where
  old := oldIncidence G length rows s
  invariant := oldIncidence_invariant G length rows paths s hs
  disc d hd := by
    rcases d with ⟨d, b⟩
    obtain ⟨i, k, rfl⟩ := exists_discAt (words G length rows) s d
    obtain ⟨r, hr⟩ := hd
    simp only [discOccurrence_at] at hr
    have F := old_occurrence_factorDisc G length rows paths s hs i r hr k.pos
    apply F.rebase
    have hh := PermutationCycles.sameCycle_map_of_step
      (ordinary G length rows paths s hs).rotation
      (ordinary G length rows paths s hs).augmented.rotation (fun e ↦ (e, false))
      (ordinary G length rows paths s hs).augmented_rotation_lifts
      (discAt_sameCycle (words G length rows) s i ⟨0, k.pos⟩ k)
    cases b
    · exact hh
    · exact hh.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))

/-- Embed the literal doubled row coordinates in their actual original occurrence. -/
noncomputable def newCoordinates (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j) :
    Darts length (fun _ : Unit ↦ j) → DiscDarts (words G length rows) s × Bool :=
  fun d ↦ (discAt (words G length rows) s i
    (Fin.cast (new_occurrence_length G length rows s i j hi).symm d.2.1), d.2.2)

omit [∀ i, NeZero (length i)] in
theorem newCoordinates_injective (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j) :
    Function.Injective (newCoordinates G length rows s i j hi) := by
  rintro ⟨⟨⟩, k, b⟩ ⟨⟨⟩, l, c⟩ h
  have hk := discAt_injective (words G length rows) s i (congrArg Prod.fst h)
  have hb := congrArg Prod.snd h
  have hkl : k = l := Fin.cast_injective _ hk
  cases hkl
  cases hb
  rfl

theorem newCoordinates_rotation (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j)
    (d : Darts length (fun _ : Unit ↦ j)) :
    newCoordinates G length rows s i j hi (rotation length (fun _ : Unit ↦ j) d) =
      (ordinary G length rows paths s hs).augmented.rotation
        (newCoordinates G length rows s i j hi d) := by
  rcases d with ⟨⟨⟩, k, b⟩
  cases b
  · rfl
  · change (discAt _ s i _, false) = (discRotation _ s (discAt _ s i _), false)
    rw [discRotation_at]
    congr 2
    apply Fin.ext
    simp only [Fin.val_cast, PermutationCycles.finRotate_value]
    rw [new_occurrence_length G length rows s i j hi]
    change (k + 1).val = (k.val + 1) % length j
    simp [Fin.val_add, Nat.add_mod_mod]

omit [∀ i, NeZero (length i)] in
theorem newCoordinates_read (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j)
    (d : Darts length (fun _ : Unit ↦ j)) :
    discRead paths (words G length rows) s (newCoordinates G length rows s i j hi d).1 =
      bif s[i].2 then (rows j d.2.1, true) else (rows j d.2.1.rev, false) := by
  rw [newCoordinates, discRead_at]
  have hh := oriented_newWord_read G length rows j s[i].2 d.2.1
  simp only [Fin.getElem_fin] at hi
  simp only [Fin.getElem_fin, hi, words, Sum.elim_inr]
  exact hh

omit [∀ i, NeZero (length i)] in
theorem newCoordinates_arc (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j)
    (d : Darts length (fun _ : Unit ↦ j)) :
    (augmentedData G length rows paths s hs).labelling.arc
        (newCoordinates G length rows s i j hi d) =
      arc length G rows (fun _ : Unit ↦ j) (fun _ ↦ s[i].2) d := by
  change ((discRead paths (words G length rows) s
    (newCoordinates G length rows s i j hi d).1).1.1, !d.2.2) = _
  rw [newCoordinates_read]
  cases hb : s[i].2 <;> rfl

omit [∀ i, NeZero (length i)] in
theorem newCoordinates_corner (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j)
    (d : Darts length (fun _ : Unit ↦ j)) :
    (augmentedData G length rows paths s hs).labelling.corner
        (newCoordinates G length rows s i j hi d) =
      corner length G rows (fun _ : Unit ↦ j) (fun _ ↦ s[i].2) d := by
  rcases d with ⟨⟨⟩, k, b⟩
  cases b
  · change coefficient G (discRead paths (words G length rows) s
        (newCoordinates G length rows s i j hi ⟨(), k, false⟩).1) = _
    rw [newCoordinates_read]
    cases hb : s[i].2
    · change (includeSyllable G (rows j k.rev))⁻¹ =
        includeSyllable G (inverseSyllable G (rows j k.rev))
      exact (include_inverse G _).symm
    · rfl
  · rfl

theorem newCoordinates_forward (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j)
    (k : Fin (length j)) :
    (augmentedData G length rows paths s hs).labelling.vertexWord
        (newCoordinates G length rows s i j hi ⟨(), k, false⟩) =
      Augmentation.word G length rows (positiveOrigin length j s[i].2 k) :=
  forward_of_coordinates length G rows (fun _ : Unit ↦ j) (fun _ ↦ s[i].2) _
    (newCoordinates G length rows s i j hi) (newCoordinates_injective G length rows s i j hi)
    (newCoordinates_rotation G length rows paths s hs i j hi)
    (newCoordinates_arc G length rows paths s hs i j hi)
    (newCoordinates_corner G length rows paths s hs i j hi) () k

theorem newCoordinates_backward (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j)
    (k : Fin (length j)) :
    (augmentedData G length rows paths s hs).labelling.reverseVertexWord
        (newCoordinates G length rows s i j hi ⟨(), k, true⟩) =
      Augmentation.word G length rows (negativeOrigin length j s[i].2 k) :=
  backward_of_coordinates length G rows (fun _ : Unit ↦ j) (fun _ ↦ s[i].2) _
    (newCoordinates G length rows s i j hi) (newCoordinates_injective G length rows s i j hi)
    (newCoordinates_rotation G length rows paths s hs i j hi)
    (newCoordinates_arc G length rows paths s hs i j hi)
    (newCoordinates_corner G length rows paths s hs i j hi) () k

omit [∀ i, NeZero (length i)] in
theorem new_coordinates_exist (d : DiscDarts (words G length rows) s × Bool)
    (hd : ¬oldIncidence G length rows s d) :
    ∃ (i : Fin s.length) (j : I) (hi : s[i].1.2 = Sum.inr j) (k : Fin (length j)),
      newCoordinates G length rows s i j hi ⟨(), k, d.2⟩ = d := by
  rcases d with ⟨d, b⟩
  obtain ⟨i, k, rfl⟩ := exists_discAt (words G length rows) s d
  have hn : ¬∃ r, s[i].1.2 = Sum.inl r := by
    simpa only [oldIncidence, discOccurrence_at] using hd
  cases hi : s[i].1.2 with
  | inl r => exact (hn ⟨r, hi⟩).elim
  | inr j =>
    refine ⟨i, j, hi, Fin.cast (new_occurrence_length G length rows s i j hi) k, ?_⟩
    change (discAt _ s i _, b) = _
    congr 2

/-- The original new incidence has a complete row reading in its actual marker direction. -/
theorem new_incidence_readings (d : DiscDarts (words G length rows) s × Bool)
    (hd : ¬oldIncidence G length rows s d) :
    ∃ o : Origin length,
      ((augmentedData G length rows paths s hs).labelling.arc d).2 = true →
        (augmentedData G length rows paths s hs).labelling.vertexWord d =
          Augmentation.word G length rows o := by
  obtain ⟨i, j, hi, k, he⟩ := new_coordinates_exist G length rows s d hd
  refine ⟨positiveOrigin length j s[i].2 k, ?_⟩
  intro ha
  have hb : d.2 = false := by
    change (!d.2) = true at ha
    cases h : d.2 <;> simp_all
  rw [hb] at he
  rw [← he]
  exact newCoordinates_forward G length rows paths s hs i j hi k

/-- Both directions share a single indexed origin chosen according to the actual marker sign. -/
theorem new_incidence_both_readings (d : DiscDarts (words G length rows) s × Bool)
    (hd : ¬oldIncidence G length rows s d) :
    ∃ o : Origin length,
      (((augmentedData G length rows paths s hs).labelling.arc d).2 = true →
        (augmentedData G length rows paths s hs).labelling.vertexWord d =
          Augmentation.word G length rows o) ∧
      (((augmentedData G length rows paths s hs).labelling.arc d).2 = false →
        (augmentedData G length rows paths s hs).labelling.reverseVertexWord d =
          Augmentation.word G length rows o) := by
  obtain ⟨i, j, hi, k, he⟩ := new_coordinates_exist G length rows s d hd
  cases hb : d.2
  · refine ⟨positiveOrigin length j s[i].2 k, ?_, ?_⟩
    · intro _
      rw [hb] at he
      rw [← he]
      exact newCoordinates_forward G length rows paths s hs i j hi k
    · intro ha
      change (!d.2) = false at ha
      simp only [hb, Bool.not_false, Bool.true_eq_false] at ha
  · refine ⟨negativeOrigin length j s[i].2 k, ?_, ?_⟩
    · intro ha
      change (!d.2) = true at ha
      simp only [hb, Bool.not_true, Bool.false_eq_true] at ha
    · intro _
      rw [hb] at he
      rw [← he]
      exact newCoordinates_backward G length rows paths s hs i j hi k

/-- The actual canonical identity supplies all old-disc and indexed new-reading hypotheses. -/
noncomputable def mixedReadings :
    MixedReadings (rows := rows) (oldDiscSystem G length rows paths s hs) where
  origin d := Classical.choose (new_incidence_both_readings G length rows paths s hs d.val d.property)
  forward d hd := (Classical.choose_spec
    (new_incidence_both_readings G length rows paths s hs d hd)).1
  backward d hd := (Classical.choose_spec
    (new_incidence_both_readings G length rows paths s hs d hd)).2

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
