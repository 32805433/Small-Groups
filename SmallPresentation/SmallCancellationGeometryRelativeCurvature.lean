module

public import SmallPresentation.SmallCancellationGeometryRelativeReadingReduction
public import SmallPresentation.SmallCancellationGeometryRelativeReduction

/-!
# The metric dipole theorem for actual augmented relative ribbon pictures

The proof performs actual inner-bigon suppression, extracts metric pieces from the retained
original opposite incidence bands, and applies Euler counting. The outside face has no
coefficient condition. Both arbitrary indexed rows and arbitrary finite ribbon dart types
are supported.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedReadings

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
variable {length : I → ℕ} [∀ i, NeZero (length i)]
variable {rows : ∀ i, Fin (length i) → Syllable G}
variable {Y : Type*} [Fintype Y] {P : RibbonMap Y}
variable {L : RibbonLabelling P A (Monoid.CoprodI G)}
variable (Q : AugmentedReadings G length rows P L)

/-- A connected spherical augmented relative picture satisfying metric small cancellation
has an actual matched pair of original incidences with the same indexed oriented origin. -/
theorem exists_matched_origin
    (hmetric : MetricSmallCancellation G length rows)
    (outside : Y) (hc : P.Connected) (hred : L.CyclicallyReduced)
    (hregions : ∀ y, ¬ P.face.SameCycle outside y → L.faceValue y = 1)
    (heuler : Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) :
    ∃ y, (L.arc y).2 = true ∧ Q.origin (P.edge y) = Q.origin y := by
  classical
  by_contra hn
  have hnodipole : ∀ y, (L.arc y).2 = true → Q.origin (P.edge y) ≠ Q.origin y := by
    intro y hy he
    exact hn ⟨y, hy, he⟩
  let R := L.taggedBlocks outside hregions
  obtain ⟨D, inst, S, _, _, _, _, hEuler, hfaces⟩ :=
    TaggedRelativeBlockRibbon.exists_reduced Y R hc
      (L.taggedBlocks_cyclicallyReduced outside hregions hred)
  let : Fintype D := inst
  have hsEuler : Fintype.card S.map.Vertex + Fintype.card S.map.Face =
      Fintype.card S.map.Edge + 2 := by
    change Fintype.card S.map.Vertex + Fintype.card S.map.Face + Fintype.card P.Edge =
      Fintype.card P.Vertex + Fintype.card P.Face + Fintype.card S.map.Edge at hEuler
    omega
  apply S.map.sphere_c6_impossible (S.map.faceOf S.outside) _ _ hsEuler
  · intro v
    induction v using Quotient.inductionOn with
    | h d =>
      change 6 ≤ incidenceDegree S.map.vertexOf (S.map.vertexOf d)
      rw [S.map.vertex_incidenceDegree]
      exact le_trans (by omega) (Q.seven_le_vertex_length S hmetric hnodipole d)
  · intro f
    induction f using Quotient.inductionOn with
    | h d =>
      intro hd
      change 3 ≤ incidenceDegree S.map.faceOf (S.map.faceOf d)
      rw [S.map.face_incidenceDegree]
      apply hfaces d
      intro hh
      exact hd (Quotient.sound hh.symm)

/-- The same actual dipole theorem with only the original indexed-row hypotheses. Cyclic
reduction and the required row-length bound are proved consequences of those hypotheses. -/
theorem exists_matched_origin_of_rows
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (outside : Y) (hc : P.Connected)
    (hregions : ∀ y, ¬ P.face.SameCycle outside y → L.faceValue y = 1)
    (heuler : Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) :
    ∃ y, (L.arc y).2 = true ∧ Q.origin (P.edge y) = Q.origin y := by
  apply Q.exists_matched_origin hmetric outside hc _ hregions heuler
  apply Q.cyclicallyReduced hidentity hreduced
  intro i
  have hh := seven_le_length_of_metric G length rows hmetric i
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedReadings
