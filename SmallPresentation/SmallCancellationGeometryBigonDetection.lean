module

public import SmallPresentation.SmallCancellationGeometryBigon
public import SmallPresentation.SmallCancellationGeometryComponents
public import SmallPresentation.SmallCancellationGeometryReduction

/-!
# Detecting inner bigons from actual face boundaries

The bigon data needed for surgery are extracted from a two-corner inner face. In particular,
distinctness of the boundary edges follows from connectivity, rather than being an additional
geometric assumption. Combined with cyclic reduction this supplies the lower bound on inner
face degrees after all bigons have been eliminated.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

variable {D : Type*} (P : RibbonMap D)

/-- A two-corner face returns after two steps. -/
theorem face_twice_of_length_two (d : D) (h : (P.faceBoundary d).length = 2) :
    P.face (P.face d) = d := by
  have hp : Function.minimalPeriod P.face d = 2 := by simpa using h
  have hh := Function.iterate_minimalPeriod (f := (P.face : D → D)) (x := d)
  simpa only [hp, Function.iterate_succ_apply, Function.iterate_zero, id_eq] using hh

/-- The two corners of a length-two face are distinct. -/
theorem face_ne_of_length_two (d : D) (h : (P.faceBoundary d).length = 2) :
    P.face d ≠ d := by
  intro he
  have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr he
  have hh : Function.minimalPeriod P.face d = 2 := by simpa using h
  omega

/-- Produce the actual surgery datum from an inner face of degree two. -/
def innerBigon (hc : P.Connected) (outside d : D)
    (hi : ¬ P.face.SameCycle outside d) (h : (P.faceBoundary d).length = 2) : Bigon P where
  left := d
  right := P.face d
  left_ne_right := (P.face_ne_of_length_two d h).symm
  mate_left_ne_right := P.inner_two_cycle_distinct_edges hc outside d (P.face d) rfl
    (P.face_twice_of_length_two d h) hi
  face_left := rfl
  face_right := P.face_twice_of_length_two d h

end RibbonMap

namespace RelativeRibbon

variable {D X H I : Type*} [Finite D] [Group H]
variable {relators : I → List (SignedLetter X × H)}
variable (P : RelativeRibbon (D := D) X H I relators)

/-- Cyclic reduction and absence of actual inner bigons give the face-degree bound used in
the spherical incidence contradiction. -/
theorem three_le_inner_face_length (hc : P.map.Connected)
    (hred : P.labelling.CyclicallyReduced)
    (hbigon : ∀ B : Bigon P.map, P.map.face.SameCycle P.outside B.left)
    (d : D) (hi : ¬ P.map.face.SameCycle P.outside d) :
    3 ≤ (P.map.faceBoundary d).length := by
  have htwo := P.two_le_inner_face_length hred d hi
  have hne : (P.map.faceBoundary d).length ≠ 2 := by
    intro hh
    exact hi (hbigon (P.map.innerBigon hc P.outside d hi hh))
  omega

end RelativeRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
