module

public import SmallPresentation.SmallCancellationGeometryMarkedBigon

/-!
# Terminating relative bigon reduction with one marked boundary vertex

The marked vertex may fail cyclic reduction. Its degree is at most two and there is another
vertex, so it cannot support a monogon. Suppression preserves this exception and all actual
original relator tags. Thus the final inner-face degree bound needs no reduction assumption
at the marked factor boundary.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RelativeBlockRibbon

variable {D Y X H I : Type*} [Group H]
    {read : Y → SignedLetter X × H} {relators : I → List Y}
    (R : RelativeBlockRibbon (D := D) Y X H I read relators)

/-- Cyclic reduction is only required away from one specified actual vertex. -/
def CyclicallyReducedExcept (marked : D) : Prop := ∀ d,
  ¬R.map.rotation.SameCycle marked d → R.corner d = 1 →
    R.firstArc (R.map.rotation d) ≠ (R.lastArc d).map reverseLetter

theorem suppress_cyclicallyReducedExcept [Finite D] (marked : D) (B : Bigon R.map)
    (hi : ¬R.map.face.SameCycle R.outside B.left) (hred : R.CyclicallyReducedExcept marked) :
    (R.suppress B hi).CyclicallyReducedExcept (B.collapse marked) := by
  intro d hd hc
  have hd' := mt (B.collapse_sameVertex_iff marked d).mpr hd
  rw [R.suppress_corner B hi] at hc
  have hx : ¬R.map.rotation.SameCycle marked (B.faceCoordinate d) := by
    intro h
    exact hd' (h.trans (B.faceCoordinate_original_vertex d).symm)
  have h := hred (B.faceCoordinate d) hx hc
  rw [R.suppress_firstArc B hi, R.suppress_lastArc B hi]
  change R.firstArc (B.rotation d).val ≠ (R.lastArc (B.faceCoordinate d)).map reverseLetter
  rw [B.rotation_exchange]
  exact h

/-- Even without cyclic reduction at a marked small vertex, inner monogons are impossible
when the connected picture contains another vertex. -/
theorem inner_face_ne_one_except [Finite D] (marked other : D)
    (hc : R.map.Connected) (hsmall : (R.map.vertexBoundary marked).length ≤ 2)
    (hother : ¬R.map.rotation.SameCycle marked other)
    (hred : R.CyclicallyReducedExcept marked) (d : D)
    (hi : ¬R.map.face.SameCycle R.outside d) : (R.map.faceBoundary d).length ≠ 1 := by
  intro hlen
  have hp : Function.minimalPeriod R.map.face d = 1 := by simpa using hlen
  have hfix := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hp
  by_cases hd : R.map.rotation.SameCycle marked d
  · exact R.map.no_monogon_at_small_vertex hc marked hsmall other hother d hd hfix
  · have hcorner : R.corner d = 1 := by
      have h := R.inner_equation d hi
      simpa [corner, RibbonMap.faceBoundary, hp] using h
    have he : R.map.edge d = R.map.rotation d := by
      have h := congrArg R.map.rotation hfix
      simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using h
    apply hred d hd hcorner
    rw [← he]
    exact R.firstArc_edge d

theorem three_le_inner_face_length_except [Finite D] (marked other : D)
    (hc : R.map.Connected) (hsmall : (R.map.vertexBoundary marked).length ≤ 2)
    (hother : ¬R.map.rotation.SameCycle marked other)
    (hred : R.CyclicallyReducedExcept marked)
    (hbigon : ∀ B : Bigon R.map, R.map.face.SameCycle R.outside B.left)
    (d : D) (hi : ¬R.map.face.SameCycle R.outside d) :
    3 ≤ (R.map.faceBoundary d).length := by
  have hpos := List.length_pos_iff.mpr (R.map.faceBoundary_nonempty d)
  have hone := R.inner_face_ne_one_except marked other hc hsmall hother hred d hi
  have htwo : (R.map.faceBoundary d).length ≠ 2 := by
    intro h
    exact hi (hbigon (R.map.innerBigon hc R.outside d hi h))
  omega

end RelativeBlockRibbon

namespace TaggedRelativeBlockRibbon

universe u

variable {Y X H I : Type*} [Group H]
    {read : Y → SignedLetter X × H} {relators : I → List Y} {opposite : Y → Y}

/-- Remove all inner bigons with one exceptional marked vertex. The returned injection
retains original relator tags and actual vertex membership, including the marked vertex. -/
theorem exists_reduced_except (D : Type u) [Fintype D]
    (R : TaggedRelativeBlockRibbon (D := D) Y X H I read relators opposite)
    (marked other : D) (hc : R.map.Connected)
    (hsmall : (R.map.vertexBoundary marked).length ≤ 2)
    (hother : ¬R.map.rotation.SameCycle marked other)
    (hred : R.toRelativeBlockRibbon.CyclicallyReducedExcept marked) :
    ∃ (E : Type u) (_ : Fintype E)
      (S : TaggedRelativeBlockRibbon (D := E) Y X H I read relators opposite)
      (m n : E) (f : E ↪ D),
      S.map.Connected ∧ S.toRelativeBlockRibbon.CyclicallyReducedExcept m ∧
      (S.map.vertexBoundary m).length ≤ 2 ∧ ¬S.map.rotation.SameCycle m n ∧
      (∀ e, S.relator e = R.relator (f e)) ∧ R.map.rotation.SameCycle marked (f m) ∧
      (∀ d e, S.map.rotation.SameCycle d e ↔ R.map.rotation.SameCycle (f d) (f e)) ∧
      Nonempty (S.map.Vertex ≃ R.map.Vertex) ∧
      Nonempty (S.map.Component ≃ R.map.Component) ∧
      Fintype.card S.map.Vertex + Fintype.card S.map.Face + Fintype.card R.map.Edge =
        Fintype.card R.map.Vertex + Fintype.card R.map.Face + Fintype.card S.map.Edge ∧
      ∀ d, ¬S.map.face.SameCycle S.outside d → 3 ≤ (S.map.faceBoundary d).length := by
  classical
  by_cases hex : ∃ B : Bigon R.map, ¬R.map.face.SameCycle R.outside B.left
  · obtain ⟨B, hi⟩ := hex
    let R' := R.suppress B hi
    have hc' : R'.map.Connected := B.connected hc
    have hr' : R'.toRelativeBlockRibbon.CyclicallyReducedExcept (B.collapse marked) :=
      R.toRelativeBlockRibbon.suppress_cyclicallyReducedExcept marked B hi hred
    have hs' : (R'.map.vertexBoundary (B.collapse marked)).length ≤ 2 :=
      (B.collapse_vertexBoundary_length_le marked).trans hsmall
    have hn' : ¬R'.map.rotation.SameCycle (B.collapse marked) (B.collapse other) := by
      intro h
      exact hother (((B.collapse_sameVertex_iff marked _).mp h).trans
        (B.collapse_original_vertex other))
    obtain ⟨E, inst, S, m, n, f, hSc, hSr, hSm, hSn, htag, hmark, hvertex,
        ⟨ev⟩, ⟨ec⟩, hEuler, hfaces⟩ :=
      exists_reduced_except B.Dart R' (B.collapse marked) (B.collapse other) hc' hs' hn' hr'
    let : Fintype E := inst
    refine ⟨E, inst, S, m, n, f.trans ⟨Subtype.val, Subtype.val_injective⟩,
      hSc, hSr, hSm, hSn, htag, ?_, ?_, ⟨ev.trans B.verticesEquiv⟩,
      ⟨ec.trans B.componentsEquiv⟩, ?_, hfaces⟩
    · exact (B.collapse_sameVertex_iff marked _).mp hmark
    · intro d e
      exact (hvertex d e).trans (B.sameVertex_iff _ _)
    · have hv := B.card_vertices
      have hf := B.card_faces
      have he := B.card_edges
      change Fintype.card S.map.Vertex + Fintype.card S.map.Face +
        Fintype.card B.suppress.Edge = Fintype.card B.suppress.Vertex +
          Fintype.card B.suppress.Face + Fintype.card S.map.Edge at hEuler
      omega
  · have hbigon : ∀ B : Bigon R.map, R.map.face.SameCycle R.outside B.left := by
      intro B
      by_contra h
      exact hex ⟨B, h⟩
    exact ⟨D, inferInstance, R, marked, other, Function.Embedding.refl D,
      hc, hred, hsmall, hother, fun _ ↦ rfl, .refl _ _, fun _ _ ↦ Iff.rfl,
      ⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, rfl,
      R.toRelativeBlockRibbon.three_le_inner_face_length_except marked other hc hsmall
        hother hred hbigon⟩
termination_by Fintype.card D
decreasing_by
  have h := B.card_darts
  omega

end TaggedRelativeBlockRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
