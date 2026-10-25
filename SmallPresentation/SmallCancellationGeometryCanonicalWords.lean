module

public import SmallPresentation.SmallCancellationGeometryIdentityPlanarity
public import SmallPresentation.SmallCancellationGeometryAugmentedLabels
public import SmallPresentation.SmallCancellationRoots
public import SmallPresentation.SmallCancellationGeometrySprayBoundary

/-!
# Literal old/new words for the canonical free presentation

Old relations are spelled in their own factor alphabet before inclusion. New relations
use the displayed positive syllable list. These choices allow the geometric construction
to distinguish old factor discs from attaching discs without a presentation assumption.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationDerivative.CanonicalSchur IdentityBoundary Homology

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)

/-- Spell a coefficient-factor relation entirely within its own factor. -/
noncomputable def oldWord (r : OldIndex G) : List (SignedLetter (Syllable G)) :=
  ((chosenSection (G r.1)).word r.2.val).map (fun x ↦ (⟨r.1, x.1⟩, x.2))

theorem oldWord_evaluates (r : OldIndex G) : FreeGroup.mk (oldWord G r) = old G r := by
  rw [oldWord, ← FreeGroup.map.mk, (chosenSection (G r.1)).evaluates]
  rfl

theorem oldWord_tag (r : OldIndex G) (x : SignedLetter (Syllable G))
    (hx : x ∈ oldWord G r) : x.1.1 = r.1 := by
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  rfl

/-- The original displayed attaching word, with no reduction or conjugation. -/
def newWord (i : I) : List (SignedLetter (Syllable G)) :=
  List.ofFn (fun p : Fin (length i) ↦ (rows i p, true))

omit [∀ a, Group (G a)] in
theorem newWord_evaluates (i : I) :
    FreeGroup.mk (newWord G length rows i) = rowLift G length rows i := by
  have h := FreeGroupCentralizer.mk_positiveWord (List.ofFn (rows i))
  simpa only [List.map_ofFn, newWord, rowLift, Function.comp_def] using h

/-- All canonical relators with their factor-respecting literal spellings. -/
noncomputable def words : OldIndex G ⊕ I → List (SignedLetter (Syllable G)) :=
  Sum.elim (oldWord G) (newWord G length rows)

theorem words_evaluate (i : OldIndex G ⊕ I) :
    FreeGroup.mk (words G length rows i) = all G (rowLift G length rows) i := by
  cases i with
  | inl r => exact oldWord_evaluates G r
  | inr i => exact newWord_evaluates G length rows i

/-- Signed coefficient reading of one literal free letter. -/
def coefficient (x : SignedLetter (Syllable G)) : Monoid.CoprodI G :=
  bif x.2 then includeSyllable G x.1 else (includeSyllable G x.1)⁻¹

@[simp] theorem coefficient_reverse (x : SignedLetter (Syllable G)) :
    coefficient G (reverseLetter x) = (coefficient G x)⁻¹ := by
  rcases x with ⟨x, b⟩
  cases b <;> simp [coefficient, reverseLetter]

theorem coefficient_eq_projection (x : SignedLetter (Syllable G)) :
    coefficient G x = FreeProductPresentation.projection G (letterValue x) := by
  rcases x with ⟨x, b⟩
  cases b <;> simp [coefficient, letterValue, FreeProductPresentation.projection,
    includeSyllable]

theorem coefficient_product (w : List (SignedLetter (Syllable G))) :
    (w.map (coefficient G)).prod = FreeProductPresentation.projection G (FreeGroup.mk w) := by
  rw [FreeProductPresentation.projection, FreeGroup.lift_mk]
  rfl

/-- Every old factor word has trivial coefficient product already in the free product. -/
theorem oldWord_product (r : OldIndex G) :
    ((oldWord G r).map (coefficient G)).prod = 1 := by
  rw [coefficient_product, oldWord_evaluates]
  exact FreeProductPresentation.factor_relations G r.1 r.2.property

variable (paths : WordSection (Syllable G))
variable (s : RelationCoordinates.Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
variable (hs : RelationCoordinates.Peiffer.evaluation (all G (rowLift G length rows)) s = 1)

include hs in
theorem identity_evaluates :
    RelationCoordinates.Peiffer.evaluation (fun i ↦ FreeGroup.mk (words G length rows i)) s = 1 := by
  simpa only [words_evaluate] using hs

/-- The actual ordinary ribbon for this canonical identity. -/
noncomputable abbrev ordinary :=
  relatorRibbon paths (words G length rows) s (identity_evaluates G length rows s hs)

/-- Actual relative marker labels on its parallel-arc augmentation. -/
noncomputable def augmentedData : (ordinary G length rows paths s hs).AugmentedData A
    (Monoid.CoprodI G) where
  tag d := (discRead paths (words G length rows) s d).1.1
  coefficient d := coefficient G (discRead paths (words G length rows) s d)
  tag_edge d := by
    have hh := relatorRibbon_edge_read paths (words G length rows) s
      (identity_evaluates G length rows s hs) d
    exact congrArg (fun x ↦ x.1.1) hh
  coefficient_edge d := by
    rw [relatorRibbon_edge_read, coefficient_reverse]

/-- All regions of this actual augmented canonical ribbon satisfy their coefficient equations. -/
theorem augmented_faceValue (d : DiscDarts (words G length rows) s × Bool) :
    (augmentedData G length rows paths s hs).labelling.faceValue d = 1 :=
  (augmentedData G length rows paths s hs).faceValue d

/-- Its Euler equation follows from the actual identity construction and parallel augmentation. -/
theorem augmented_euler :
    let P := (ordinary G length rows paths s hs).augmented
    Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component := by
  apply (RibbonMap.augmented_euler_iff _).mpr
  exact relatorRibbon_euler paths (words G length rows) s _

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
