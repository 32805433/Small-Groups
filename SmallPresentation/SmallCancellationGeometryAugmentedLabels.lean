module

public import SmallPresentation.SmallCancellationGeometryAugmentedRibbon
public import SmallPresentation.SmallCancellationGeometryRelativeFaces
public import SmallPresentation.SmallCancellationGeometryReduction

/-!
# Coefficients and exact boundary readings of parallel-arc augmentation

An original dart carries a factor tag and a coefficient, reversed at its edge mate.
Its two new incidences read `x_a g x_a⁻¹`. Every actual face has coefficient product one,
and every actual vertex reads the literal doubled original word.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D X H : Type*} [Group H] (P : RibbonMap D)

/-- Replace each departure by its leading and trailing marker departures. -/
def doubleBoundary (l : List D) : List (D × Bool) :=
  l.flatMap (fun d ↦ [(d, false), (d, true)])

theorem doubleBoundary_walk {d e : D} {l : List D}
    (h : PermutationCycles.Walk P.rotation d e l) :
    PermutationCycles.Walk P.augmented.rotation (d, false) (e, false)
      (doubleBoundary l) := by
  induction h with
  | nil => exact .nil _
  | cons d e l h ih =>
    exact .cons _ _ _ (.cons _ _ _ ih)

theorem doubleBoundary_nodup {l : List D} (h : l.Nodup) : (doubleBoundary l).Nodup := by
  have hb : ([false, true] : List Bool).Nodup := by decide
  exact h.product hb

/-- The exact based vertex boundary, with each old incidence doubled in place. -/
theorem augmented_vertexBoundary [Finite D] (d : D) :
    P.augmented.vertexBoundary (d, false) = doubleBoundary (P.vertexBoundary d) := by
  symm
  apply (P.doubleBoundary_walk (PermutationCycles.cycleBoundary_walk P.rotation d)).eq_cycleBoundary
  · intro he
    have hm : (d, false) ∈ doubleBoundary (PermutationCycles.cycleBoundary P.rotation d) := by
      apply List.mem_flatMap.mpr
      exact ⟨d, PermutationCycles.mem_cycleBoundary_self P.rotation d, by simp⟩
    rw [he] at hm
    exact List.not_mem_nil hm
  · exact doubleBoundary_nodup (P.vertexBoundary_nodup d)

/-- Tags are unchanged and coefficients inverted at the two ends of an old edge. -/
structure AugmentedData (X H : Type*) [Group H] where
  tag : D → X
  coefficient : D → H
  tag_edge : ∀ d, tag (P.edge d) = tag d
  coefficient_edge : ∀ d, coefficient (P.edge d) = (coefficient d)⁻¹

namespace AugmentedData

variable {P} (L : P.AugmentedData X H)

/-- The actual augmented arc and corner labels. -/
def labelling : RibbonLabelling P.augmented X H where
  arc d := (L.tag d.1, !d.2)
  corner d := if d.2 then 1 else L.coefficient d.1
  edge_arc d := by
    rcases d with ⟨d, b⟩
    cases b <;> simp [augmented_edge, L.tag_edge, reverseLetter]

@[simp] theorem corner_false (d : D) : L.labelling.corner (d, false) = L.coefficient d := rfl

@[simp] theorem corner_true (d : D) : L.labelling.corner (d, true) = 1 := rfl

/-- Exact ordered vertex reading, including coefficients and both marker occurrences. -/
theorem vertexWord [Finite D] (d : D) :
    L.labelling.vertexWord (d, false) =
      (P.vertexBoundary d).flatMap (fun e ↦
        [((L.tag e, true), L.coefficient e), ((L.tag e, false), 1)]) := by
  rw [RibbonLabelling.vertexWord, P.augmented_vertexBoundary]
  simp [doubleBoundary, List.map_flatMap, labelling]

/-- Each leading face is the two-sided region along one original edge. -/
theorem faceBoundary_false [Finite D] (d : D) :
    P.augmented.faceBoundary (d, false) = [(d, false), (P.edge d, false)] := by
  symm
  have hw : PermutationCycles.Walk P.augmented.face (d, false) (d, false)
      [(d, false), (P.edge d, false)] := by
    have hlast : P.augmented.face (P.edge d, false) = (d, false) := by
      rw [augmented_face_false, P.edge_involutive d]
    apply PermutationCycles.Walk.cons
    apply PermutationCycles.Walk.cons
    rw [augmented_face_false, hlast]
    exact .nil _
  apply hw.eq_cycleBoundary (by simp)
  simp only [List.nodup_cons, List.mem_singleton, Prod.mk.injEq, and_true,
    List.not_mem_nil, List.nodup_nil, and_true]
  exact ⟨(P.edge_ne d).symm, not_false⟩

/-- Each trailing face has the original face's ordered boundary with trivial coefficients. -/
theorem faceBoundary_true [Finite D] (d : D) :
    P.augmented.faceBoundary (d, true) = (P.faceBoundary d).map (fun e ↦ (e, true)) := by
  symm
  exact PermutationCycles.cycleBoundary_map_injective P.face P.augmented.face
    (fun e ↦ (e, true)) (fun _ _ h ↦ congrArg Prod.fst h) (fun _ ↦ rfl) d

/-- All face equations follow from the original inverse-edge coefficient law. -/
theorem faceValue [Finite D] (d : D × Bool) : L.labelling.faceValue d = 1 := by
  rcases d with ⟨d, b⟩
  cases b
  · simp [RibbonLabelling.faceValue, faceBoundary_false, L.coefficient_edge]
  · simp [RibbonLabelling.faceValue, faceBoundary_true, List.map_map, labelling,
      Function.comp_def]

/-- Nonidentity coefficients and different consecutive factor tags give cyclic reduction. -/
theorem cyclicallyReduced (hn : ∀ d, L.coefficient d ≠ 1)
    (ht : ∀ d, L.tag (P.rotation d) ≠ L.tag d) : L.labelling.CyclicallyReduced := by
  rintro ⟨d, b⟩ hc
  cases b
  · exact (hn d hc).elim
  · intro he
    exact ht d (congrArg Prod.fst he)

end AugmentedData
end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
