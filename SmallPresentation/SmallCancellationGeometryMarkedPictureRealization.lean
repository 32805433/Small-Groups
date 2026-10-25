module

public import SmallPresentation.SmallCancellationGeometryMarkedPicture

/-!
# Realizing marked relative pictures from null factor elements

The reserved one-syllable boundary is used only to construct a picture. All genuine
attaching vertices retain the original row indices; the metric is never imposed on the
reserved row. The resulting picture uses no factor-injectivity assumption.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRealization

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology
open AugmentedOccurrence

attribute [local instance] Classical.propDecidable

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)
    [∀ i, NeZero (length i)] (a : A) (g : G a)
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = (FreeGroup.of ⟨a, g⟩)⁻¹)
    (paths : WordSection (Syllable G))

omit [∀ i, NeZero (length i)] in
/-- The distinguished boundary is not one of the canonical factor-relation discs. -/
theorem marked_not_old : ¬(oldDiscs G length rows a g s hs paths).old
    (markedDisc G length rows a g s, false) := by
  rintro ⟨r, hr⟩
  change (markedSequence G s)[discOccurrence (extendedWords G length rows a g)
    (markedSequence G s) (markedDisc G length rows a g s)].1.2 = Sum.inl r at hr
  have hb := (marked_vertex_iff G length rows a g s hs paths
    (markedDisc G length rows a g s, false)).mp (.refl _ _)
  rw [hb] at hr
  contradiction

omit [∀ i, NeZero (length i)] in
/-- All initial corner coefficients lie in the displayed factors and obey the marker phases. -/
theorem initial_factorCorners : RibbonLabelling.FactorCorners G
    (data G length rows a g s hs paths).labelling := by
  constructor
  · rintro ⟨d, b⟩
    cases b <;> rfl
  · rintro ⟨d, b⟩ hb
    cases b
    · rfl
    · contradiction
  · rintro ⟨d, b⟩ hb
    cases b
    · contradiction
    · rfl
  · rintro ⟨d, b⟩
    cases b
    · change CanonicalWords.coefficient G
        (discRead paths (extendedWords G length rows a g) (markedSequence G s) d) ∈
          (Monoid.CoprodI.of : G (discRead paths (extendedWords G length rows a g)
            (markedSequence G s) d).1.1 →* Monoid.CoprodI G).range
      generalize discRead paths (extendedWords G length rows a g) (markedSequence G s) d = x
      rcases x with ⟨⟨t, c⟩, sign⟩
      cases sign
      · exact ⟨c⁻¹, map_inv _ c⟩
      · exact ⟨c, rfl⟩
    · exact one_mem _

omit [∀ i, NeZero (length i)] in
/-- The marked two-marker vertex has the genuine shape of a factor boundary. -/
theorem initial_shape : FactorVertexShape (data G length rows a g s hs paths).labelling
    (markedDisc G length rows a g s, false) := by
  refine ⟨?_, fun d _ ↦ (initial_factorCorners G length rows a g s hs paths).alternating d,
    fun d _ ↦ (initial_factorCorners G length rows a g s hs paths).negative_one d⟩
  intro d hd
  have hm := ((ordinary G length rows a g s hs paths).augmented.mem_vertexBoundary_iff _ d).mpr hd
  rw [marked_boundary] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> rfl

/-- Each genuine row incidence has one original indexed origin for both readings. -/
theorem original_both_readings
    (d : DiscDarts (extendedWords G length rows a g) (markedSequence G s) × Bool)
    (ho : ¬(oldDiscs G length rows a g s hs paths).old d)
    (hm : ¬(ordinary G length rows a g s hs paths).augmented.rotation.SameCycle
      (markedDisc G length rows a g s, false) d) :
    ∃ o : Origin length,
      (((data G length rows a g s hs paths).labelling.arc d).2 = true →
        (data G length rows a g s hs paths).labelling.vertexWord d =
          Augmentation.word G length rows o) ∧
      (((data G length rows a g s hs paths).labelling.arc d).2 = false →
        (data G length rows a g s hs paths).labelling.reverseVertexWord d =
          Augmentation.word G length rows o) := by
  obtain hd | hd | ⟨i, j, hi, k, he⟩ := incidence_classification G length rows a g s hs paths d
  · exact (ho hd).elim
  · exact (hm hd).elim
  · cases hb : d.2
    · refine ⟨positiveOrigin length j (markedSequence G s)[i].2 k, ?_, ?_⟩
      · intro _
        rw [hb] at he
        rw [← he]
        exact originalCoordinates_forward G length rows a g s hs paths i j hi k
      · intro ha
        change (!d.2) = false at ha
        simp only [hb, Bool.not_false, Bool.true_eq_false] at ha
    · refine ⟨negativeOrigin length j (markedSequence G s)[i].2 k, ?_, ?_⟩
      · intro ha
        change (!d.2) = true at ha
        simp only [hb, Bool.not_true, Bool.false_eq_true] at ha
      · intro _
        rw [hb] at he
        rw [← he]
        exact originalCoordinates_backward G length rows a g s hs paths i j hi k

/-- Restricting the marked incidence classification supplies the required original row readings. -/
noncomputable def component_readings : MarkedMixedReadings G length rows
    (componentOldDiscs G length rows a g s hs paths) (componentMarked G length rows a g s hs paths) where
  origin d := Classical.choose (original_both_readings G length rows a g s hs paths d.val.val
    d.property.1 (fun h ↦ d.property.2 ((ordinary G length rows a g s hs paths).augmented
      |>.restrict_sameVertex_iff _ _ _ _ _ |>.mpr h)))
  forward d hd ha := by
    rw [RibbonLabelling.restrict_vertexWord]
    exact (Classical.choose_spec (original_both_readings G length rows a g s hs paths d.val hd.1
      (fun h ↦ hd.2 ((ordinary G length rows a g s hs paths).augmented
        |>.restrict_sameVertex_iff _ _ _ _ _ |>.mpr h)))).1 ha
  backward d hd ha := by
    rw [RibbonLabelling.restrict_reverseVertexWord]
    exact (Classical.choose_spec (original_both_readings G length rows a g s hs paths d.val hd.1
      (fun h ↦ hd.2 ((ordinary G length rows a g s hs paths).augmented
        |>.restrict_sameVertex_iff _ _ _ _ _ |>.mpr h)))).2 ha

/-- A concrete null-word picture is a marked counterexample with all obligations supplied. -/
noncomputable def picture (hg : g ≠ 1) : MarkedRelativePicture G length rows
    {d : DiscDarts (extendedWords G length rows a g) (markedSequence G s) × Bool //
      (ordinary G length rows a g s hs paths).augmented.SameComponent
        (markedDisc G length rows a g s, false) d} where
  map := component G length rows a g s hs paths
  labels := componentLabels G length rows a g s hs paths
  marked := componentMarked G length rows a g s hs paths
  marked_size := component_marked_size G length rows a g s hs paths
  oldDiscs := componentOldDiscs G length rows a g s hs paths
  marked_not_old := marked_not_old G length rows a g s hs paths
  shape := by
    let F := initial_shape G length rows a g s hs paths
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      exact F.tag d.val ((ordinary G length rows a g s hs paths).augmented
        |>.restrict_sameVertex_iff _ _ _ _ _ |>.mp hd)
    · intro d _
      exact (initial_factorCorners G length rows a g s hs paths).alternating d.val
    · intro d _
      exact (initial_factorCorners G length rows a g s hs paths).negative_one d.val
  nontrivial := by
    rw [component_marked_product]
    intro h
    exact hg (Monoid.CoprodI.of_injective _ (h.trans (map_one _).symm))
  readings := component_readings G length rows a g s hs paths
  factorCorners := {
    alternating := fun d ↦ (initial_factorCorners G length rows a g s hs paths).alternating d.val
    positive_tag := fun d ↦ (initial_factorCorners G length rows a g s hs paths).positive_tag d.val
    negative_one := fun d ↦ (initial_factorCorners G length rows a g s hs paths).negative_one d.val
    coefficient := fun d ↦ (initial_factorCorners G length rows a g s hs paths).coefficient d.val }
  connected := component_connected G length rows a g s hs paths
  euler := component_euler G length rows a g s hs paths
  faces := component_faces G length rows a g s hs paths

/-- Failure of one factor embedding produces a finite marked counterexample picture. -/
theorem exists_picture (a : A) (g : G a) (hg : factorMap G length rows a g = 1)
    (hne : g ≠ 1) : ∃ (D : Type) (_ : Fintype D),
      Nonempty (MarkedRelativePicture G length rows D) := by
  obtain ⟨s, hs⟩ := exists_inverse_sequence G length rows a g hg
  exact ⟨_, inferInstance, ⟨picture G length rows a g s hs (chosenSection _) hne⟩⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRealization
