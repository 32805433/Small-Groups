module

public import SmallPresentation.SmallCancellationGeometryCanonicalReadings
public import SmallPresentation.SmallCancellationGeometryMarkedNormalization

/-!
# Actual marked pictures for null factor elements

A single extra row index is reserved for the literal boundary syllable. It is not subject
to the small-cancellation condition. Kernel membership in the original row quotient supplies
a finite identity with exactly one positive occurrence of this marked boundary row.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRealization

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)

/-- Reserve `none` for the one-syllable marked factor boundary. -/
def markedLength : Option I → ℕ
  | none => 1
  | some i => length i

instance [∀ i, NeZero (length i)] (j : Option I) : NeZero (markedLength length j) := by
  cases j
  · exact ⟨by change 1 ≠ 0; omega⟩
  · exact inferInstanceAs (NeZero (length _))

/-- Original attaching rows are retained literally; the distinguished row is one factor syllable. -/
def markedRows (a : A) (g : G a) : ∀ j, Fin (markedLength length j) → Syllable G
  | none => fun _ ↦ ⟨a, g⟩
  | some i => rows i

/-- Include old and original new labels without using the reserved boundary label. -/
def includeIndex : OldIndex G ⊕ I → OldIndex G ⊕ Option I :=
  Sum.map id some

omit [∀ a, Group (G a)] in
@[simp] theorem marked_rowLift_none (a : A) (g : G a) :
    rowLift G (markedLength length) (markedRows G length rows a g) none =
      FreeGroup.of ⟨a, g⟩ := by
  simp [rowLift, markedLength, markedRows, List.ofFn_succ]

omit [∀ a, Group (G a)] in
@[simp] theorem marked_rowLift_some (a : A) (g : G a) (i : I) :
    rowLift G (markedLength length) (markedRows G length rows a g) (some i) =
      rowLift G length rows i := rfl

@[simp] theorem marked_all_include (a : A) (g : G a) (i : OldIndex G ⊕ I) :
    all G (rowLift G (markedLength length) (markedRows G length rows a g))
      (includeIndex G i) = all G (rowLift G length rows) i := by
  cases i <;> rfl

/-- A null factor syllable lies in the actual canonical free-presentation relation subgroup. -/
theorem generator_mem_relations_of_factorMap_eq_one [∀ i, NeZero (length i)]
    (a : A) (g : G a) (hg : factorMap G length rows a g = 1) :
    FreeGroup.of (⟨a, g⟩ : Syllable G) ∈ TargetRelations G (rowLift G length rows) := by
  have hr : (fun i ↦ FreeProductPresentation.projection G (rowLift G length rows i)) =
      relatorValue G length rows := funext (projection_rowLift G length rows)
  have hbase : baseQuotientMap G (rowLift G length rows)
      (FreeProductPresentation.projection G (FreeGroup.of (⟨a, g⟩ : Syllable G))) = 1 := by
    change (QuotientGroup.mk' (Subgroup.normalClosure (Set.range
      (fun i ↦ FreeProductPresentation.projection G (rowLift G length rows i)))))
        (Monoid.CoprodI.of g) = 1
    rw [hr]
    exact hg
  apply (QuotientGroup.eq_one_iff _).mp
  change quotient G (rowLift G length rows) (FreeGroup.of ⟨a, g⟩) = 1
  rw [← presentationEquiv_quotient_projection, hbase, map_one]

/-- Normal-closure membership supplies a finite, signed list of actual conjugated relators. -/
theorem exists_inverse_sequence [∀ i, NeZero (length i)]
    (a : A) (g : G a) (hg : factorMap G length rows a g = 1) :
    ∃ s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I),
      Peiffer.evaluation (all G (rowLift G length rows)) s = (FreeGroup.of ⟨a, g⟩)⁻¹ := by
  have hmem := (TargetRelations G (rowLift G length rows)).inv_mem
    (generator_mem_relations_of_factorMap_eq_one G length rows a g hg)
  change (FreeGroup.of (⟨a, g⟩ : Syllable G))⁻¹ ∈
    Relations (all G (rowLift G length rows)) at hmem
  rw [← conjugateEvaluation_range] at hmem
  obtain ⟨w, hw⟩ := hmem
  induction w using Quot.inductionOn with
  | h s => exact ⟨s, (Peiffer.evaluation_mk _ s).symm.trans hw⟩

/-- Relabel an original occurrence while preserving its conjugator and sign. -/
def includeOccurrence (t : Peiffer.Occurrence (FreeGroup (Syllable G)) (OldIndex G ⊕ I)) :
    Peiffer.Occurrence (FreeGroup (Syllable G)) (OldIndex G ⊕ Option I) :=
  ((t.1.1, includeIndex G t.1.2), t.2)

/-- The distinguished boundary is the first and only occurrence of `none`. -/
def markedSequence (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I)) :
    Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ Option I) :=
  ((1, Sum.inr none), true) :: s.map (includeOccurrence G)

theorem evaluation_include (a : A) (g : G a)
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I)) :
    Peiffer.evaluation (all G (rowLift G (markedLength length) (markedRows G length rows a g)))
      (s.map (includeOccurrence G)) = Peiffer.evaluation (all G (rowLift G length rows)) s := by
  unfold Peiffer.evaluation
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨⟨f, i⟩, sign⟩ _
  cases sign <;> simp [includeOccurrence, Peiffer.term]

/-- Appending the reserved boundary yields an actual freely trivial relator identity. -/
theorem markedSequence_identity (a : A) (g : G a)
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = (FreeGroup.of ⟨a, g⟩)⁻¹) :
    Peiffer.evaluation (all G (rowLift G (markedLength length) (markedRows G length rows a g)))
      (markedSequence G s) = 1 := by
  change Peiffer.term _ ((1, Sum.inr none), true) *
    Peiffer.evaluation _ (s.map (includeOccurrence G)) = 1
  rw [evaluation_include, hs]
  simp [Peiffer.term]

variable [∀ i, NeZero (length i)]

/-- Every original occurrence remains different from the reserved marked label. -/
theorem includeIndex_ne_boundary (i : OldIndex G ⊕ I) :
    includeIndex G i ≠ Sum.inr none := by
  cases i <;> simp [includeIndex]

/-- The reserved boundary label occurs precisely at the first list position. -/
theorem markedSequence_boundary_iff
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (i : Fin (markedSequence G s).length) :
    (markedSequence G s)[i].1.2 = Sum.inr none ↔ i.val = 0 := by
  rcases i with ⟨n, hn⟩
  change (markedSequence G s)[n].1.2 = Sum.inr none ↔ n = 0
  unfold markedSequence at hn ⊢
  cases n with
  | zero => simp
  | succ n =>
    have hn' : n < s.length := by
      simpa only [List.length_cons, List.length_map, Nat.succ_lt_succ_iff] using hn
    simp only [List.getElem_cons_succ, List.getElem_map]
    exact iff_of_false (includeIndex_ne_boundary G s[n].1.2) (by omega)

variable (a : A) (g : G a)
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = (FreeGroup.of ⟨a, g⟩)⁻¹)
    (paths : WordSection (Syllable G))

noncomputable abbrev extendedWords :=
  CanonicalWords.words G (markedLength length) (markedRows G length rows a g)

/-- The reserved boundary occurrence in the actual finite identity list. -/
def markedOccurrence : Fin (markedSequence G s).length := ⟨0, by simp [markedSequence]⟩

omit [∀ i, NeZero (length i)] in
theorem marked_word :
    orientedWord (extendedWords G length rows a g
      (markedSequence G s)[markedOccurrence G s].1.2)
      (markedSequence G s)[markedOccurrence G s].2 = [(⟨a, g⟩, true)] := by
  simp [extendedWords, markedOccurrence, markedSequence, CanonicalWords.words,
    CanonicalWords.newWord, markedRows, markedLength, orientedWord, List.ofFn_succ]

/-- The distinguished original boundary dart before parallel augmentation. -/
noncomputable def markedDisc : DiscDarts (extendedWords G length rows a g) (markedSequence G s) :=
  discAt (extendedWords G length rows a g) (markedSequence G s) (markedOccurrence G s)
    ⟨0, by rw [marked_word]; simp⟩

noncomputable abbrev ordinary := CanonicalWords.ordinary G (markedLength length)
  (markedRows G length rows a g) paths (markedSequence G s)
  (markedSequence_identity G length rows a g s hs)

noncomputable abbrev data := CanonicalWords.augmentedData G (markedLength length)
  (markedRows G length rows a g) paths (markedSequence G s)
  (markedSequence_identity G length rows a g s hs)

omit [∀ i, NeZero (length i)] in
/-- The actual marked boundary spells the original single syllable with its positive sign. -/
theorem marked_disc_reading :
    ((ordinary G length rows a g s hs paths).vertexBoundary (markedDisc G length rows a g s)).map
      (discRead paths (extendedWords G length rows a g) (markedSequence G s)) =
      [(⟨a, g⟩, true)] := by
  rw [markedDisc, IdentityBoundary.vertex_read_at_zero]
  exact marked_word G length rows a g s

omit [∀ i, NeZero (length i)] in
/-- Exactly two markers occur at the distinguished boundary vertex of the initial picture. -/
theorem marked_boundary :
    (ordinary G length rows a g s hs paths).augmented.vertexBoundary
      (markedDisc G length rows a g s, false) =
      [(markedDisc G length rows a g s, false), (markedDisc G length rows a g s, true)] := by
  have hh := congrArg List.length (marked_disc_reading G length rows a g s hs paths)
  simp only [List.length_map, List.length_cons, List.length_nil] at hh
  have hp : Function.minimalPeriod (ordinary G length rows a g s hs paths).rotation
      (markedDisc G length rows a g s) = 1 := by simpa only [RibbonMap.vertexBoundary_length] using hh
  rw [RibbonMap.augmented_vertexBoundary]
  simp [RibbonMap.vertexBoundary, hp, RibbonMap.doubleBoundary, List.ofFn_succ]

omit [∀ i, NeZero (length i)] in
/-- The boundary coefficient product is the original factor element embedded in the free product. -/
theorem marked_product :
    (((ordinary G length rows a g s hs paths).augmented.vertexBoundary
      (markedDisc G length rows a g s, false)).map
      (data G length rows a g s hs paths).labelling.corner).prod =
      Monoid.CoprodI.of g := by
  rw [RibbonMap.AugmentedData.vertex_coefficient_product]
  have hh := congrArg (fun l : List (SignedLetter (Syllable G)) ↦
      (l.map (CanonicalWords.coefficient G)).prod)
    (marked_disc_reading G length rows a g s hs paths)
  change ((ordinary G length rows a g s hs paths).vertexBoundary
    (markedDisc G length rows a g s) |>.map (fun d ↦ CanonicalWords.coefficient G
      (discRead paths (extendedWords G length rows a g) (markedSequence G s) d))).prod = _
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, CanonicalWords.coefficient, Bool.cond_true,
    includeSyllable] using hh

omit [∀ i, NeZero (length i)] in
/-- Every initial face equation holds, including the outer face of the marked component. -/
theorem initial_faces (d : DiscDarts (extendedWords G length rows a g) (markedSequence G s) × Bool) :
    (data G length rows a g s hs paths).labelling.faceValue d = 1 :=
  CanonicalWords.augmented_faceValue G (markedLength length) (markedRows G length rows a g)
    paths (markedSequence G s) (markedSequence_identity G length rows a g s hs) d

omit [∀ i, NeZero (length i)] in
/-- Initial marked pictures are spherical on all their actual connected components. -/
theorem initial_euler : (ordinary G length rows a g s hs paths).augmented.EulerEquality :=
  CanonicalWords.augmented_euler G (markedLength length) (markedRows G length rows a g)
    paths (markedSequence G s) (markedSequence_identity G length rows a g s hs)

/-- Old factor relations in the marked picture retain the full canonical normalization system. -/
noncomputable abbrev oldDiscs := CanonicalWords.oldDiscSystem G (markedLength length)
  (markedRows G length rows a g) paths (markedSequence G s)
  (markedSequence_identity G length rows a g s hs)

omit [∀ i, NeZero (length i)] in
/-- A nontrivial factor element gives a genuinely nontrivial marked coefficient product. -/
theorem marked_product_ne_one (hg : g ≠ 1) :
    (((ordinary G length rows a g s hs paths).augmented.vertexBoundary
      (markedDisc G length rows a g s, false)).map
      (data G length rows a g s hs paths).labelling.corner).prod ≠ 1 := by
  rw [marked_product]
  intro h
  exact hg (Monoid.CoprodI.of_injective _ (h.trans (map_one _).symm))

omit [∀ i, NeZero (length i)] in
/-- The reserved label identifies exactly the actual marked vertex, not merely a row value. -/
theorem marked_vertex_iff
    (d : DiscDarts (extendedWords G length rows a g) (markedSequence G s) × Bool) :
    (ordinary G length rows a g s hs paths).augmented.rotation.SameCycle
      (markedDisc G length rows a g s, false) d ↔
    (markedSequence G s)[discOccurrence (extendedWords G length rows a g)
      (markedSequence G s) d.1].1.2 = Sum.inr none := by
  let W := extendedWords G length rows a g
  let t := markedSequence G s
  let P := ordinary G length rows a g s hs paths
  constructor
  · intro h
    have hp := PermutationCycles.sameCycle_map_of_step P.augmented.rotation P.rotation Prod.fst
      P.augmented_rotation_projects h
    have ho := (disc_sameCycle_iff W t _ _).mp hp
    change discOccurrence W t (markedDisc G length rows a g s) = discOccurrence W t d.1 at ho
    rw [markedDisc, discOccurrence_at] at ho
    apply (markedSequence_boundary_iff G s _).mpr
    exact congrArg Fin.val ho.symm
  · intro h
    have hv := (markedSequence_boundary_iff G s _).mp h
    have ho : discOccurrence W t d.1 = markedOccurrence G s := Fin.ext hv
    have hp : P.rotation.SameCycle (markedDisc G length rows a g s) d.1 := by
      apply (disc_sameCycle_iff W t _ _).mpr
      rw [markedDisc, discOccurrence_at]
      exact ho.symm
    have hh := PermutationCycles.sameCycle_map_of_step P.rotation P.augmented.rotation
      (fun e ↦ (e, false)) P.augmented_rotation_lifts hp
    rcases d with ⟨d, b⟩
    cases b
    · exact hh
    · exact hh.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))

/-- Literal coordinates for an original attaching row inside the extended marked picture. -/
noncomputable abbrev originalCoordinates (i : Fin (markedSequence G s).length) (j : I)
    (hi : (markedSequence G s)[i].1.2 = Sum.inr (some j)) :=
  CanonicalWords.newCoordinates G (markedLength length) (markedRows G length rows a g)
    (markedSequence G s) i (some j) hi

/-- New rows retain the original indexed forward word, with no marked-row metric hypothesis. -/
theorem originalCoordinates_forward (i : Fin (markedSequence G s).length) (j : I)
    (hi : (markedSequence G s)[i].1.2 = Sum.inr (some j)) (k : Fin (length j)) :
    (data G length rows a g s hs paths).labelling.vertexWord
      (originalCoordinates G length rows a g s i j hi ⟨(), k, false⟩) =
    Augmentation.word G length rows (AugmentedOccurrence.positiveOrigin length j
      (markedSequence G s)[i].2 k) := by
  exact CanonicalWords.newCoordinates_forward G (markedLength length)
    (markedRows G length rows a g) paths (markedSequence G s)
    (markedSequence_identity G length rows a g s hs) i (some j) hi k

/-- The reverse word is retained with the original row label and sign as well. -/
theorem originalCoordinates_backward (i : Fin (markedSequence G s).length) (j : I)
    (hi : (markedSequence G s)[i].1.2 = Sum.inr (some j)) (k : Fin (length j)) :
    (data G length rows a g s hs paths).labelling.reverseVertexWord
      (originalCoordinates G length rows a g s i j hi ⟨(), k, true⟩) =
    Augmentation.word G length rows (AugmentedOccurrence.negativeOrigin length j
      (markedSequence G s)[i].2 k) := by
  exact CanonicalWords.newCoordinates_backward G (markedLength length)
    (markedRows G length rows a g) paths (markedSequence G s)
    (markedSequence_identity G length rows a g s hs) i (some j) hi k

omit [∀ i, NeZero (length i)] in
/-- Each incidence belongs to an old factor disc, the unique marked vertex, or one original
attaching-row coordinate. Empty old rows produce no unaccounted vertex. -/
theorem incidence_classification
    (d : DiscDarts (extendedWords G length rows a g) (markedSequence G s) × Bool) :
    (oldDiscs G length rows a g s hs paths).old d ∨
    (ordinary G length rows a g s hs paths).augmented.rotation.SameCycle
      (markedDisc G length rows a g s, false) d ∨
    ∃ (i : Fin (markedSequence G s).length) (j : I)
      (hi : (markedSequence G s)[i].1.2 = Sum.inr (some j)) (k : Fin (length j)),
      originalCoordinates G length rows a g s i j hi ⟨(), k, d.2⟩ = d := by
  classical
  by_cases hold : (oldDiscs G length rows a g s hs paths).old d
  · exact Or.inl hold
  · right
    obtain ⟨i, j, hi, k, hk⟩ := CanonicalWords.new_coordinates_exist G (markedLength length)
      (markedRows G length rows a g) (markedSequence G s) d hold
    cases j with
    | none =>
      left
      apply (marked_vertex_iff G length rows a g s hs paths d).mpr
      rw [← hk]
      simpa only [CanonicalWords.newCoordinates, discOccurrence_at] using hi
    | some j => exact Or.inr ⟨i, j, hi, k, hk⟩

/-- Retain the actual connected component of the distinguished boundary. -/
noncomputable abbrev component := (ordinary G length rows a g s hs paths).augmented.componentRibbon
  (markedDisc G length rows a g s, false)

/-- The labels on this component are the original labels restricted along inclusion. -/
noncomputable abbrev componentLabels := (data G length rows a g s hs paths).labelling.restrict
  ((ordinary G length rows a g s hs paths).augmented.SameComponent
    (markedDisc G length rows a g s, false))
  ((ordinary G length rows a g s hs paths).augmented.component_membership_edge _)
  ((ordinary G length rows a g s hs paths).augmented.component_membership_rotation _)

/-- The original distinguished dart, considered inside its actual component. -/
noncomputable def componentMarked : {d : DiscDarts (extendedWords G length rows a g)
    (markedSequence G s) × Bool // (ordinary G length rows a g s hs paths).augmented.SameComponent
      (markedDisc G length rows a g s, false) d} :=
  ⟨(markedDisc G length rows a g s, false), Relation.EqvGen.refl _⟩

omit [∀ i, NeZero (length i)] in
theorem component_connected : (component G length rows a g s hs paths).Connected :=
  (ordinary G length rows a g s hs paths).augmented.componentRibbon_connected _

omit [∀ i, NeZero (length i)] in
theorem component_euler : (component G length rows a g s hs paths).EulerEquality :=
  (ordinary G length rows a g s hs paths).augmented.restrict_euler _ _ _
    (initial_euler G length rows a g s hs paths)

omit [∀ i, NeZero (length i)] in
theorem component_faces (d) : (componentLabels G length rows a g s hs paths).faceValue d = 1 := by
  rw [RibbonLabelling.restrict_faceValue]
  exact initial_faces G length rows a g s hs paths d.val

omit [∀ i, NeZero (length i)] in
theorem component_boundary_map :
    ((component G length rows a g s hs paths).vertexBoundary
      (componentMarked G length rows a g s hs paths)).map Subtype.val =
    (ordinary G length rows a g s hs paths).augmented.vertexBoundary
      (markedDisc G length rows a g s, false) :=
  (ordinary G length rows a g s hs paths).augmented.restrict_vertexBoundary
    ((ordinary G length rows a g s hs paths).augmented.SameComponent
      (markedDisc G length rows a g s, false))
    ((ordinary G length rows a g s hs paths).augmented.component_membership_edge _)
    ((ordinary G length rows a g s hs paths).augmented.component_membership_rotation _)
    (componentMarked G length rows a g s hs paths)

omit [∀ i, NeZero (length i)] in
theorem component_marked_size :
    ((component G length rows a g s hs paths).vertexBoundary
      (componentMarked G length rows a g s hs paths)).length = 2 := by
  have hh := congrArg List.length (component_boundary_map G length rows a g s hs paths)
  rw [List.length_map, marked_boundary] at hh
  exact hh

omit [∀ i, NeZero (length i)] in
theorem component_marked_product :
    (((component G length rows a g s hs paths).vertexBoundary
      (componentMarked G length rows a g s hs paths)).map
        (componentLabels G length rows a g s hs paths).corner).prod = Monoid.CoprodI.of g := by
  change (((component G length rows a g s hs paths).vertexBoundary
    (componentMarked G length rows a g s hs paths)).map
      ((data G length rows a g s hs paths).labelling.corner ∘ Subtype.val)).prod = _
  rw [← List.map_map, component_boundary_map]
  exact marked_product G length rows a g s hs paths

/-- The normalization system on the marked connected component is inherited by actual restriction. -/
noncomputable abbrev componentOldDiscs := (oldDiscs G length rows a g s hs paths).restrict
  ((ordinary G length rows a g s hs paths).augmented.SameComponent
    (markedDisc G length rows a g s, false))
  ((ordinary G length rows a g s hs paths).augmented.component_membership_edge _)
  ((ordinary G length rows a g s hs paths).augmented.component_membership_rotation _)

/-- A null factor element has a concrete connected spherical marked picture with all
region equations valid and the original element as its two-incidence boundary coefficient. -/
theorem exists_marked_component (a : A) (g : G a)
    (hg : factorMap G length rows a g = 1) (paths : WordSection (Syllable G)) :
    ∃ (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
      (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = (FreeGroup.of ⟨a, g⟩)⁻¹),
      (component G length rows a g s hs paths).Connected ∧
      (component G length rows a g s hs paths).EulerEquality ∧
      (∀ d, (componentLabels G length rows a g s hs paths).faceValue d = 1) ∧
      ((component G length rows a g s hs paths).vertexBoundary
        (componentMarked G length rows a g s hs paths)).length = 2 ∧
      (((component G length rows a g s hs paths).vertexBoundary
        (componentMarked G length rows a g s hs paths)).map
          (componentLabels G length rows a g s hs paths).corner).prod = Monoid.CoprodI.of g := by
  obtain ⟨s, hs⟩ := exists_inverse_sequence G length rows a g hg
  exact ⟨s, hs, component_connected G length rows a g s hs paths,
    component_euler G length rows a g s hs paths, component_faces G length rows a g s hs paths,
    component_marked_size G length rows a g s hs paths,
    component_marked_product G length rows a g s hs paths⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRealization
