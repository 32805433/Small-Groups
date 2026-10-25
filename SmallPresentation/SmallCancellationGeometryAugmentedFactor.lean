module

public import SmallPresentation.SmallCancellationGeometryFactorDisc

/-! Literal augmentation of a constant-factor relation is an erasable factor disc. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap.AugmentedData

open PermutationCycles

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}
    (L : P.AugmentedData X H) (a : D)

/-- The doubled boundary has exactly the original coefficient product. -/
theorem vertex_coefficient_product :
    ((P.augmented.vertexBoundary (a, false)).map L.labelling.corner).prod =
      ((P.vertexBoundary a).map L.coefficient).prod := by
  rw [P.augmented_vertexBoundary]
  have hh (l : List D) :
      ((doubleBoundary l).map L.labelling.corner).prod = (l.map L.coefficient).prod := by
    induction l with
    | nil => rfl
    | cons d l ih => simpa [doubleBoundary, List.flatMap_cons] using ih
  exact hh _

/-- Constant factor tags and a trivial original product supply all normalization invariants. -/
theorem factorDisc (htag : ∀ d, P.rotation.SameCycle a d → L.tag d = L.tag a)
    (hproduct : ((P.vertexBoundary a).map L.coefficient).prod = 1) :
    FactorDisc L.labelling (a, false) := by
  refine ⟨?_, ?_, ?_, (L.vertex_coefficient_product a).trans hproduct⟩
  · intro d hd
    exact htag d.1 (sameCycle_map_of_step P.augmented.rotation P.rotation Prod.fst
      P.augmented_rotation_projects hd)
  · rintro ⟨d, b⟩ _
    cases b <;> rfl
  · rintro ⟨d, b⟩ _ hb
    cases b
    · contradiction
    · rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap.AugmentedData
