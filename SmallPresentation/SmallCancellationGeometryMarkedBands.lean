module

public import SmallPresentation.SmallCancellationGeometryMarkedBoundary
public import SmallPresentation.SmallCancellationGeometryRelativeMetric

/-!
# Bounds for bands meeting a marked two-incidence vertex

A boundary band opposite a marked vertex does not need a small-cancellation hypothesis
against a fictitious relator. Its length is bounded by the actual number of original
marked incidences. Alternating signs then give at most one positive marker per band.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.TaggedRelativeBlockRibbon

variable {D Y X H : Type*} [Finite D] [Group H]
    {read : Y → SignedLetter X × H} (P : RibbonMap Y)
    (R : TaggedRelativeBlockRibbon (D := D) Y X H Y read P.vertexBoundary P.edge)

omit [Finite D] in
/-- Compressing nonempty blocks cannot increase the degree of any recorded original vertex. -/
theorem vertex_length_le_original (d : D) :
    (R.map.vertexBoundary d).length ≤ (P.vertexBoundary (R.relator d)).length := by
  have hlen (l : List D) : l.length ≤ (l.flatMap R.block).length := by
    induction l with
    | nil => simp
    | cons e l ih =>
      have hp : 0 < (R.block e).length := List.length_pos_iff.mpr (R.block_nonempty e)
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega
  rw [← R.relator_word d]
  exact hlen _

/-- Every block opposite a marked vertex fits inside the marked vertex's original boundary. -/
theorem block_length_le_opposite (d : D) :
    (R.block d).length ≤ (P.vertexBoundary (R.relator (R.map.edge d))).length := by
  rw [RibbonMap.vertexBoundary_length, ← R.edge_block_length P d]
  exact R.block_length_le P (R.map.edge d)

/-- A band opposite a two-incidence marked vertex contains at most one positive marker. -/
theorem block_count_le_one_of_short_opposite (sign : Y → Bool) (d : D)
    (hshort : (P.vertexBoundary (R.relator (R.map.edge d))).length ≤ 2)
    (hchain : (R.block d).IsChain (fun y z ↦ sign z = !(sign y))) :
    (R.block d).countP sign ≤ 1 := by
  have hlen := le_trans (R.block_length_le_opposite P d) hshort
  cases he : R.block d with
  | nil => simp
  | cons a tail =>
    have hh := AlternatingBlock.count_positive sign a tail (by simpa only [he] using hchain)
    simp only [he] at hlen ⊢
    rw [hh]
    cases sign a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The actual marked-boundary band satisfies the same strict numerical bound needed
for curvature whenever the relator on the other side has at least seven syllables. -/
theorem block_metric_bound_of_short_opposite (sign : Y → Bool) (d : D) (length : ℕ)
    (hshort : (P.vertexBoundary (R.relator (R.map.edge d))).length ≤ 2)
    (hchain : (R.block d).IsChain (fun y z ↦ sign z = !(sign y)))
    (hlength : 7 ≤ length) : 6 * (R.block d).countP sign < length := by
  have hh := R.block_count_le_one_of_short_opposite P sign d hshort hchain
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.TaggedRelativeBlockRibbon
