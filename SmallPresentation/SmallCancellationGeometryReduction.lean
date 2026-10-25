module

public import SmallPresentation.SmallCancellationGeometryRibbonCounts

/-!
# Cyclic reduction excludes inner monogons

This is the first local diagram-reduction lemma on the actual ribbon representation. An inner
face with one corner has trivial corner coefficient and adjacent inverse arc letters, contradicting
cyclic reduction. The outer face is explicitly exempt. Bridge surgery preserves cyclic reduction
because it preserves vertex words, although planarity and general relative region equations still
need separate arguments.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonLabelling

variable {D X H : Type*} [Group H] {P : RibbonMap D} (L : RibbonLabelling P X H)

/-- No identity corner separates mutually inverse adjacent free letters. -/
def CyclicallyReduced : Prop :=
  ∀ d, L.corner d = 1 → L.arc (P.rotation d) ≠ reverseLetter (L.arc d)

/-- Equal-label bridge surgery retains the exact cyclic-reduction condition at every vertex. -/
theorem bridge_cyclicallyReduced (hred : L.CyclicallyReduced) (a b : D)
    (h : L.arc a = L.arc b) : (L.bridge a b h).CyclicallyReduced := hred

end RibbonLabelling

namespace RelativeRibbon

variable {D X H I : Type*} [Group H] {relators : I → List (SignedLetter X × H)}
variable (P : RelativeRibbon (D := D) X H I relators)

/-- Cyclic reduction rules out an inner face containing just one corner. -/
theorem inner_face_ne_one (hred : P.labelling.CyclicallyReduced) (d : D)
    (hinner : ¬P.map.face.SameCycle P.outside d) : (P.map.faceBoundary d).length ≠ 1 := by
  intro hlen
  have hp : Function.minimalPeriod P.map.face d = 1 := by simpa using hlen
  have hfix : P.map.face d = d := by
    have h := Function.iterate_minimalPeriod (f := (P.map.face : D → D)) (x := d)
    simpa only [hp, Function.iterate_one] using h
  have hb : P.map.faceBoundary d = [d] := by
    simp [RibbonMap.faceBoundary, hp]
  have hc : P.labelling.corner d = 1 := by
    have h := P.inner_equation d hinner
    simpa only [RibbonLabelling.faceValue, hb, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, inv_eq_one] using h
  have he : P.map.edge d = P.map.rotation d := by
    have h := congrArg P.map.rotation hfix
    simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using h
  apply hred d hc
  rw [← he]
  exact P.labelling.edge_arc d

/-- Every actual inner face has at least two incidences before bigon suppression. -/
theorem two_le_inner_face_length [Finite D] (hred : P.labelling.CyclicallyReduced) (d : D)
    (hinner : ¬P.map.face.SameCycle P.outside d) : 2 ≤ (P.map.faceBoundary d).length := by
  have hn := P.map.faceBoundary_nonempty d
  have hone := P.inner_face_ne_one hred d hinner
  have hpos := List.length_pos_iff.mpr hn
  omega

end RelativeRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
