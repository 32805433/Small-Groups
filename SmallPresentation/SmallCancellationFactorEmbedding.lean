module

public import SmallPresentation.SmallCancellationGeometryMarkedReplacement
public import SmallPresentation.SmallCancellationDipolePairMatchedReplacement

/-!
# Metric relative small cancellation preserves the actual coefficient factors

A nontrivial null factor element gives a finite marked spherical picture. Minimize its
actual attaching-vertex count and then its dart count. Concrete corner cancellation and
face capping remove all old factor discs. Marked curvature then supplies two matching
attaching vertices. Actual inverse-pair replacement turns them into proved factor discs,
preserving every region equation and strictly reducing the attaching count.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] (T : MarkedRelativePicture G length rows D)

/-- The explicit metric condition excludes every actual minimal marked counterexample. -/
theorem not_minimal_of_metric
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) : ¬T.Minimal := by
  classical
  intro hmin
  let R := Minimal.readingsExcept T hmin
  obtain ⟨a, ha, hpos, hb, hmatch⟩ := Minimal.matched_origin T hmin hidentity hreduced hmetric
  have hnegative : (T.labels.arc (T.map.edge a)).2 = false := by
    rw [T.labels.edge_arc]
    change (!(T.labels.arc a).2) = false
    rw [hpos]
    rfl
  let o := R.origin a
  have hforward : T.labels.vertexWord a = Augmentation.word G length rows o := R.forward a ha hpos
  have hbackward : T.labels.reverseVertexWord (T.map.edge a) =
      Augmentation.word G length rows o := by
    rw [R.backward (T.map.edge a) hb hnegative]
    exact congrArg (Augmentation.word G length rows) hmatch
  let W := MatchedPair.replacement G length rows T.labels a (T.map.edge a) o
    hforward hbackward hnegative hmetric T.factorCorners rfl
  have hW : ∀ d, d ∈ Set.range W.embedding ↔
      T.map.rotation.SameCycle a d ∨ T.map.rotation.SameCycle (T.map.edge a) d :=
    MatchedPair.replacement_range G length rows T.labels a (T.map.edge a) o
      hforward hbackward hnegative hmetric T.factorCorners rfl
  have hmarked : T.marked ∉ Set.range W.embedding := by
    intro h
    rcases (hW T.marked).mp h with h | h
    · exact ha h.symm
    · exact hb h.symm
  have hdistinct : ¬T.map.rotation.SameCycle W.point (T.map.edge W.point) :=
    MatchedPair.replacement_distinct G length rows T.labels a (T.map.edge a) o
      hforward hbackward hnegative hmetric T.factorCorners rfl
  have hlt := replacement_count_lt T W.map W.labels
    (W.oldDiscs T.oldDiscs) (Set.range W.embedding)
    (W.selected_invariant T.map.rotation (PairFactorBlocks.source _) W.rotation) hmarked
    (fun _ ↦ Iff.rfl) W.rotation_outside (fun _ _ ↦ rfl) W.corner_outside
    (W.factorCorners T.factorCorners) (W.euler T.euler hdistinct)
    (W.faces T.factorCorners T.faces hdistinct) a
    ⟨Minimal.no_old T hmin a, ha⟩ ((hW a).mpr (Or.inl (.refl _ _)))
  exact Minimal.not_fewer_rows T hmin _ hlt

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)

/-- Factor injectivity from the fully constructed marked-picture reduction argument. -/
theorem factor_injective_of_metric
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    ∀ a, Function.Injective (factorMap G length rows a) := by
  apply Geometry.MarkedRealization.factor_injective_of_no_minimal_picture G length rows
  intro D _ T
  exact T.not_minimal_of_metric hidentity hreduced hmetric

end SmallPresentationStatements.RelativeSmallCancellation
