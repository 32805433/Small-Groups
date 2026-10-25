module

public import SmallPresentation.SmallCancellationGeometryMarkedReadings
public import SmallPresentation.SmallCancellationGeometryRelativeReadingReduction

/-!
# Metric dipoles in pictures with a marked factor boundary

Only nonboundary vertices are required to carry relator words. The marked vertex has at
most two actual incidences. Bands incident to it use the direct incidence bound, and its
possible failure of cyclic reduction is handled by the proved monogon-isolation theorem.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedReadingsExcept

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {Y : Type*} [Fintype Y] {P : RibbonMap Y}
    {L : RibbonLabelling P A (Monoid.CoprodI G)} {marked : Y}
    (Q : AugmentedReadingsExcept G length rows P L marked)

/-- The C-prime metric condition forces a matched pair of genuine row incidences even
when a marked factor boundary is present. No artificial relator is assigned to that boundary. -/
theorem exists_matched_origin
    (hmetric : MetricSmallCancellation G length rows)
    (hsmall : (P.vertexBoundary marked).length ≤ 2)
    (outside other : Y) (hother : ¬P.rotation.SameCycle marked other) (hc : P.Connected)
    (hred : ∀ y, ¬P.rotation.SameCycle marked y → L.corner y = 1 →
      L.arc (P.rotation y) ≠ reverseLetter (L.arc y))
    (hregions : ∀ y, ¬P.face.SameCycle outside y → L.faceValue y = 1)
    (heuler : Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) :
    ∃ y, ¬P.rotation.SameCycle marked y ∧ (L.arc y).2 = true ∧
      ¬P.rotation.SameCycle marked (P.edge y) ∧ Q.origin (P.edge y) = Q.origin y := by
  classical
  by_contra hn
  have hnodipole : ∀ y, ¬P.rotation.SameCycle marked y → (L.arc y).2 = true →
      ¬P.rotation.SameCycle marked (P.edge y) → Q.origin (P.edge y) ≠ Q.origin y := by
    intro y hy hs he hmatch
    exact hn ⟨y, hy, hs, he, hmatch⟩
  let R := L.taggedBlocks outside hregions
  have hRred : R.toRelativeBlockRibbon.CyclicallyReducedExcept marked := by
    intro y hy hc
    have hh := hred y hy hc
    simpa [RelativeBlockRibbon.firstArc, RelativeBlockRibbon.lastArc,
      RibbonLabelling.taggedBlocks, R] using hh
  obtain ⟨D, inst, S, m, n, f, _, _, _, _, htag, hmark, hvertex,
      _, _, hEuler, hfaces⟩ :=
    TaggedRelativeBlockRibbon.exists_reduced_except Y R marked other hc hsmall hother hRred
  let : Fintype D := inst
  have hsEuler : Fintype.card S.map.Vertex + Fintype.card S.map.Face =
      Fintype.card S.map.Edge + 2 := by
    change Fintype.card S.map.Vertex + Fintype.card S.map.Face + Fintype.card P.Edge =
      Fintype.card P.Vertex + Fintype.card P.Face + Fintype.card S.map.Edge at hEuler
    omega
  apply Geometry.sphere_c6_boundary_impossible S.map.vertexOf S.map.edgeOf S.map.faceOf
    (S.map.vertexOf m) (S.map.faceOf S.outside) S.map.edge_incidenceDegree _ _ _ hsEuler
  · intro v
    induction v using Quotient.inductionOn with
    | h d =>
      intro hd
      change 6 ≤ incidenceDegree S.map.vertexOf (S.map.vertexOf d)
      rw [S.map.vertex_incidenceDegree]
      have hregular : ¬P.rotation.SameCycle marked (S.relator d) := by
        intro h
        have htag' : S.relator d = f d := htag d
        rw [htag'] at h
        have hv := (hvertex m d).mpr (hmark.symm.trans h)
        exact hd (Quotient.sound hv.symm)
      exact le_trans (by omega) (Q.seven_le_vertex_length S hmetric hsmall hnodipole d hregular)
  · rw [S.map.vertex_incidenceDegree]
    exact List.length_pos_iff.mpr (S.map.vertexBoundary_nonempty m)
  · intro v
    induction v using Quotient.inductionOn with
    | h d =>
      intro hd
      change 3 ≤ incidenceDegree S.map.faceOf (S.map.faceOf d)
      rw [S.map.face_incidenceDegree]
      apply hfaces d
      intro hh
      exact hd (Quotient.sound hh.symm)

include Q in
omit [Fintype Y] in
/-- Original cyclic row reduction supplies exactly the reduction needed away from the
marked boundary; no condition is imposed at the marked factor vertex. -/
theorem cyclicallyReduced_except
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 2 ≤ length i) :
    ∀ y, ¬P.rotation.SameCycle marked y → L.corner y = 1 →
      L.arc (P.rotation y) ≠ reverseLetter (L.arc y) := by
  intro y hy hc he
  have hs : (L.arc y).2 = false := by
    cases hs : (L.arc y).2 with
    | false => rfl
    | true =>
      have hh := OppositeBand.forward_reading G length rows L y (Q.origin y)
        (Q.forward y hy hs) 0 (by have := Fin.pos (Q.origin y).position; omega)
      have hcorner := congrArg Prod.snd hh
      simp only [Function.iterate_zero_apply] at hcorner
      exact (syllableAt_include_ne_one hidentity (Q.origin y) 0 (hcorner.symm.trans hc)).elim
  let p := P.rotation.symm y
  have hpreg : ¬P.rotation.SameCycle marked p := by
    intro h
    have hh := Equiv.Perm.sameCycle_apply_right.mpr h
    change P.rotation.SameCycle marked (P.rotation (P.rotation.symm y)) at hh
    rw [Equiv.apply_symm_apply] at hh
    exact hy hh
  have hp : (L.arc p).2 = true := by
    have hh := Q.alternating p hpreg
    simpa [p, hs] using hh.symm
  have h0 := OppositeBand.forward_reading G length rows L p (Q.origin p)
    (Q.forward p hpreg hp) 1 (by have := hlength (Q.origin p).row; omega)
  have h1 := OppositeBand.forward_reading G length rows L p (Q.origin p)
    (Q.forward p hpreg hp) 2 (by have := hlength (Q.origin p).row; omega)
  have ht0 := congrArg (fun x ↦ x.1.1) h0
  have ht1 := congrArg (fun x ↦ x.1.1) h1
  have htags := syllableAt_zero_tag_ne_one hreduced (Q.origin p)
  apply htags
  have he' := congrArg Prod.fst he
  simp [p, Augmentation.entry, Function.iterate_succ_apply'] at ht0 ht1
  exact ht0.symm.trans (he'.symm.trans ht1)

/-- Marked-boundary dipole extraction from only the original indexed row assumptions. -/
theorem exists_matched_origin_of_rows
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (hsmall : (P.vertexBoundary marked).length ≤ 2)
    (outside other : Y) (hother : ¬P.rotation.SameCycle marked other) (hc : P.Connected)
    (hregions : ∀ y, ¬P.face.SameCycle outside y → L.faceValue y = 1)
    (heuler : Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) :
    ∃ y, ¬P.rotation.SameCycle marked y ∧ (L.arc y).2 = true ∧
      ¬P.rotation.SameCycle marked (P.edge y) ∧ Q.origin (P.edge y) = Q.origin y := by
  apply Q.exists_matched_origin hmetric hsmall outside other hother hc _ hregions heuler
  apply Q.cyclicallyReduced_except hidentity hreduced
  intro i
  have hh := seven_le_length_of_metric G length rows hmetric i
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedReadingsExcept
