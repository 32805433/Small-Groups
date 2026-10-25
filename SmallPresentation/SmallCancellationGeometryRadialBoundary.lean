module

public import SmallPresentation.SmallCancellationGeometryRadial
public import SmallPresentation.SmallCancellationGeometryBoundaryTheorem

/-!
# The missing outer-region equation follows from old vertex equations

The radial ribbon turns corner coefficients into honest inverse edge labels. Its
vertex words are exactly the old vertex coefficient products and the inverse-corner
face products. The nonabelian planar boundary theorem therefore recovers the sole
omitted region equation whenever all original vertices evaluate to one.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D K : Type*} [Group K] [Finite D] (P : RibbonMap D)

theorem radial_vertexBoundary_false (d : D) :
    P.radial.vertexBoundary (d, false) = (P.vertexBoundary d).map (fun e ↦ (e, false)) := by
  exact (cycleBoundary_map_injective P.rotation P.radial.rotation (fun e ↦ (e, false))
    (fun _ _ h ↦ congrArg Prod.fst h) (fun _ ↦ rfl) d).symm

theorem radial_vertexBoundary_true (d : D) :
    P.radial.vertexBoundary (d, true) = (P.faceBoundary d).map (fun e ↦ (e, true)) := by
  exact (cycleBoundary_map_injective P.face P.radial.rotation (fun e ↦ (e, true))
    (fun _ _ h ↦ congrArg Prod.fst h) (fun _ ↦ rfl) d).symm

def radialWeight (corner : D → K) : D × Bool → K
  | (d, false) => corner d
  | (d, true) => (corner d)⁻¹

omit [Finite D] in
theorem radialWeight_edge (corner : D → K) (d : D × Bool) :
    radialWeight corner (P.radial.edge d) = (radialWeight corner d)⁻¹ := by
  rcases d with ⟨d, b⟩
  cases b
  · rfl
  · change corner d = ((corner d)⁻¹)⁻¹
    rw [inv_inv]

theorem radial_vertex_product_false (corner : D → K) (d : D) :
    ((P.radial.vertexBoundary (d, false)).map (radialWeight corner)).prod =
      ((P.vertexBoundary d).map corner).prod := by
  rw [P.radial_vertexBoundary_false, List.map_map]
  rfl

theorem radial_vertex_product_true (corner : D → K) (d : D) :
    ((P.radial.vertexBoundary (d, true)).map (radialWeight corner)).prod =
      ((P.faceBoundary d).map (fun e ↦ (corner e)⁻¹)).prod := by
  rw [P.radial_vertexBoundary_true, List.map_map]
  rfl

/-- On a connected spherical old-only coefficient picture, the sole exceptional face also
has trivial boundary product. No commutativity or inverse-edge rule on corners is assumed. -/
theorem outside_corner_product_one [Fintype D] (corner : D → K)
    (hc : P.Connected) (hE : P.EulerEquality) (outside : D)
    (hvertex : ∀ d, ((P.vertexBoundary d).map corner).prod = 1)
    (hfaces : ∀ d, ¬P.face.SameCycle outside d →
      ((P.faceBoundary d).map (fun e ↦ (corner e)⁻¹)).prod = 1) :
    ((P.faceBoundary outside).map (fun e ↦ (corner e)⁻¹)).prod = 1 := by
  have h := boundary_product_one (D × Bool) P.radial (radialWeight corner)
    (P.radialWeight_edge corner) (P.radial_connected hc) (P.radial_euler_iff.mpr hE)
    (outside, true) ?_
  · rw [P.radial_vertex_product_true] at h
    exact h
  · rintro ⟨d, b⟩ hd
    cases b
    · rw [P.radial_vertex_product_false]
      exact hvertex d
    · rw [P.radial_vertex_product_true]
      apply hfaces d
      intro hf
      apply hd
      exact sameCycle_map_of_step P.face P.radial.rotation (fun e ↦ (e, true))
        (fun _ ↦ Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) hf

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
