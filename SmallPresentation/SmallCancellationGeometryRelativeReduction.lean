module

public import SmallPresentation.SmallCancellationGeometryRelativeTagged
public import SmallPresentation.SmallCancellationGeometryBigonCounts

/-!
# Terminating bigon reduction with original incidence tags

Repeated actual inner-bigon suppression terminates by the number of darts. The resulting
relative block picture retains every original based vertex reading and exact edge-tag
reversal, has the same vertices and components, preserves Euler characteristic, and has
inner face degree at least three. No planarity or metric hypothesis is used in this step.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.TaggedRelativeBlockRibbon

universe u

variable {D : Type u} {Y X H I : Type*} [Group H]
variable {read : Y → SignedLetter X × H} {relators : I → List Y} {opposite : Y → Y}

/-- All inner bigons can be removed while preserving actual relative block data and Euler
characteristic. The input ribbon may have arbitrary genus; connectedness is the only global
graph condition needed to exclude the degenerate doubled-edge inner face. -/
theorem exists_reduced (D : Type u) [Fintype D]
    (R : TaggedRelativeBlockRibbon (D := D) Y X H I read relators opposite)
    (hc : R.map.Connected) (hred : R.toRelativeBlockRibbon.CyclicallyReduced) :
    ∃ (E : Type u) (_ : Fintype E)
      (S : TaggedRelativeBlockRibbon (D := E) Y X H I read relators opposite),
      S.map.Connected ∧ S.toRelativeBlockRibbon.CyclicallyReduced ∧
      Nonempty (S.map.Vertex ≃ R.map.Vertex) ∧
      Nonempty (S.map.Component ≃ R.map.Component) ∧
      Fintype.card S.map.Vertex + Fintype.card S.map.Face + Fintype.card R.map.Edge =
        Fintype.card R.map.Vertex + Fintype.card R.map.Face + Fintype.card S.map.Edge ∧
      ∀ d, ¬ S.map.face.SameCycle S.outside d → 3 ≤ (S.map.faceBoundary d).length := by
  classical
  by_cases hex : ∃ B : Bigon R.map, ¬ R.map.face.SameCycle R.outside B.left
  · obtain ⟨B, hi⟩ := hex
    let R' := R.suppress B hi
    have hc' : R'.map.Connected := B.connected hc
    have hr' : R'.toRelativeBlockRibbon.CyclicallyReduced :=
      R.toRelativeBlockRibbon.suppress_cyclicallyReduced B hi hred
    obtain ⟨E, inst, S, hSc, hSr, ⟨ev⟩, ⟨ec⟩, hEuler, hfaces⟩ :=
      exists_reduced B.Dart R' hc' hr'
    refine ⟨E, inst, S, hSc, hSr, ⟨ev.trans B.verticesEquiv⟩,
      ⟨ec.trans B.componentsEquiv⟩, ?_, hfaces⟩
    have hv := B.card_vertices
    have hf := B.card_faces
    have he := B.card_edges
    change Fintype.card S.map.Vertex + Fintype.card S.map.Face +
      Fintype.card B.suppress.Edge = Fintype.card B.suppress.Vertex +
        Fintype.card B.suppress.Face + Fintype.card S.map.Edge at hEuler
    omega
  · have hbigon : ∀ B : Bigon R.map, R.map.face.SameCycle R.outside B.left := by
      intro B
      by_contra hi
      exact hex ⟨B, hi⟩
    exact ⟨D, inferInstance, R, hc, hred, ⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, rfl,
      R.toRelativeBlockRibbon.three_le_inner_face_length hc hred hbigon⟩
termination_by Fintype.card D
decreasing_by
  have h := B.card_darts
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.TaggedRelativeBlockRibbon
