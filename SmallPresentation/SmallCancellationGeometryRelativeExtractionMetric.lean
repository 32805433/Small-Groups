module

public import SmallPresentation.SmallCancellationGeometryRelativeExtraction
public import SmallPresentation.SmallCancellationGeometryRelativeCurvature

/-!
# Metric dipoles extracted from genuine mixed relative pictures

Old-disc normalization retains exact indexed readings and quotient paths. Thus the metric
curvature theorem produces matching original new incidences, with quotient-path agreement
proved from the actual surviving edge rather than assumed as a conjugator condition.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.OldDiscExtraction

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D Q : Type*} [Finite D] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)}
    {q : Monoid.CoprodI G →* Q} {S : OldDiscSystem L} {F : CornerPotential L q}
    (W : OldDiscExtraction S F) (R : MixedReadings (rows := rows) S)

/-- The output of old-disc extraction carries the original indexed readings literally. -/
noncomputable def readings : AugmentedReadings G length rows W.map W.label where
  origin d := R.origin ⟨W.inclusion d, W.new d⟩
  forward d hd := by
    rw [W.forward d]
    apply R.forward (W.inclusion d) (W.new d)
    simpa only [W.arc] using hd
  backward d hd := by
    rw [W.backward d]
    apply R.backward (W.inclusion d) (W.new d)
    simpa only [W.arc] using hd

include W in
omit [Finite D] in
/-- The actual reduced-picture edge gives two distinct original new incidences with the
same indexed oriented origin and the same quotient path potential. -/
theorem exists_matched_original
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    ∃ (d e : D) (hd : ¬S.old d) (he : ¬S.old e),
      d ≠ e ∧ (L.arc d).2 = true ∧ L.arc e = reverseLetter (L.arc d) ∧
      R.origin ⟨e, he⟩ = R.origin ⟨d, hd⟩ ∧ F.value e = F.value d := by
  classical
  let : Fintype W.Dart := Fintype.ofFinite W.Dart
  have hE : Fintype.card W.map.Vertex + Fintype.card W.map.Face =
      Fintype.card W.map.Edge + 2 := by
    have hh := W.euler
    have hc := W.map.card_components_of_connected W.connected W.outside
    simpa only [RibbonMap.EulerEquality, hc, mul_one] using hh
  obtain ⟨d, hd, he⟩ := (W.readings R).exists_matched_origin_of_rows
    hidentity hreduced hmetric W.outside W.connected W.regions hE
  refine ⟨W.inclusion d, W.inclusion (W.map.edge d), W.new d, W.new (W.map.edge d),
    ?_, ?_, ?_, he, ?_⟩
  · intro h
    exact W.map.edge_ne d (W.inclusion.injective h).symm
  · simpa only [W.arc] using hd
  · rw [← W.arc, ← W.arc]
    exact W.label.edge_arc d
  · rw [← W.value, ← W.value]
    exact W.potential.edge d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.OldDiscExtraction
