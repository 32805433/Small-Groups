module

public import SmallPresentation.SmallCancellationGeometryRadialBoundary
public import SmallPresentation.SmallCancellationGeometryRelativeRestriction

/-! Recovering the outer-region equation on one actual connected component. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D K : Type*} [Group K] [Fintype D] (P : RibbonMap D)

/-- The outer-region theorem applied to one component of a possibly disconnected spherical
ribbon. All hypotheses and the conclusion refer to the original incidence set. -/
theorem component_outside_corner_product_one (corner : D → K)
    (hE : P.EulerEquality) (outside : D)
    (hvertex : ∀ d, P.SameComponent outside d →
      ((P.vertexBoundary d).map corner).prod = 1)
    (hfaces : ∀ d, P.SameComponent outside d → ¬P.face.SameCycle outside d →
      ((P.faceBoundary d).map (fun e ↦ (corner e)⁻¹)).prod = 1) :
    ((P.faceBoundary outside).map (fun e ↦ (corner e)⁻¹)).prod = 1 := by
  classical
  let Q := P.componentRibbon outside
  let o : {d : D // P.SameComponent outside d} := ⟨outside, Relation.EqvGen.refl _⟩
  have hQE : Q.EulerEquality := P.restrict_euler _ _ _ hE
  have hv (d : {d : D // P.SameComponent outside d}) :
      ((Q.vertexBoundary d).map (fun e ↦ corner e.val)).prod = 1 := by
    change ((Q.vertexBoundary d).map (corner ∘ Subtype.val)).prod = 1
    rw [← List.map_map]
    change (((P.restrict _ _ _).vertexBoundary d).map Subtype.val |>.map corner).prod = 1
    rw [P.restrict_vertexBoundary]
    exact hvertex d.val d.property
  have hf (d : {d : D // P.SameComponent outside d})
      (hd : ¬Q.face.SameCycle o d) :
      ((Q.faceBoundary d).map (fun e ↦ (corner e.val)⁻¹)).prod = 1 := by
    change ((Q.faceBoundary d).map ((fun e ↦ (corner e)⁻¹) ∘ Subtype.val)).prod = 1
    rw [← List.map_map]
    change (((P.restrict _ _ _).faceBoundary d).map Subtype.val |>.map
      (fun e ↦ (corner e)⁻¹)).prod = 1
    rw [P.restrict_faceBoundary]
    apply hfaces d.val d.property
    intro h
    exact hd ((P.restrict_sameFace_iff _ _ _ o d).mpr h)
  have hh := Q.outside_corner_product_one (fun e ↦ corner e.val)
    (P.componentRibbon_connected outside) hQE o hv hf
  change ((Q.faceBoundary o).map ((fun e ↦ (corner e)⁻¹) ∘ Subtype.val)).prod = 1 at hh
  rw [← List.map_map] at hh
  change (((P.restrict _ _ _).faceBoundary o).map Subtype.val |>.map
    (fun e ↦ (corner e)⁻¹)).prod = 1 at hh
  rw [P.restrict_faceBoundary] at hh
  exact hh

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
