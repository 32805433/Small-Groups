module

public import SmallPresentation.SmallCancellationGeometryMatchedVertices

/-! Literal factor-block coordinates for a matched pair of actual attaching vertices. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MatchedPair

open PermutationCycles

variable {A I : Type} (G : A → Type) [∀ x, Group (G x)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    {D : Type*} [Finite D] {P : RibbonMap D} (L : RibbonLabelling P A (Monoid.CoprodI G))
    (a b : D) (o : Origin length)
    (hforward : L.vertexWord a = Augmentation.word G length rows o)
    (hbackward : L.reverseVertexWord b = Augmentation.word G length rows o)
    (hnegative : (L.arc b).2 = false) (hmetric : MetricSmallCancellation G length rows)

include hforward in
omit [Finite D] in
theorem forwardPeriod : Function.minimalPeriod P.rotation a = 2 * length o.row := by
  simpa [RibbonLabelling.vertexWord] using congrArg List.length hforward

include hbackward in
omit [Finite D] in
theorem backwardPeriod : Function.minimalPeriod P.rotation b = 2 * length o.row := by
  simpa using congrArg List.length hbackward

/-- The exact marker embedding of both matched original attaching vertices. -/
noncomputable def embedding : (Fin (length o.row) ⊕ Fin (length o.row)) × Bool ↪ D :=
  pairOrbitEmbedding P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward)
    (matched_readings_distinct_vertices G length rows P L hmetric a b o
      hforward hbackward hnegative)

local notation "f" => embedding G length rows L a b o hforward hbackward hnegative hmetric

theorem first_false (k : Fin (length o.row)) :
    f (.inl k, false) = P.rotation^[2 * k.val] a := by
  exact pairOrbitMap_left P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward) k false

theorem first_true (k : Fin (length o.row)) :
    f (.inl k, true) = P.rotation^[2 * k.val + 1] a := by
  exact pairOrbitMap_left P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward) k true

theorem second_false (k : Fin (length o.row)) :
    f (.inr k, false) = P.rotation.symm^[2 * k.rev.val + 1] b :=
  pairOrbitMap_right_false_reverse P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward) k

theorem second_true (k : Fin (length o.row)) :
    f (.inr k, true) = P.rotation.symm^[2 * k.rev.val] b :=
  pairOrbitMap_right_true_reverse P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward) k

theorem rotation (d : (Fin (length o.row) ⊕ Fin (length o.row)) × Bool) :
    f (doublePerm (Equiv.sumCongr (finRotate (length o.row))
      (finRotate (length o.row))) d) = P.rotation (f d) :=
  pairOrbitMap_rotation P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward) d

theorem anchor_first : f (.inl 0, false) = a :=
  pairOrbitMap_anchor_left P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward)

theorem anchor_second : f (.inr (0 : Fin (length o.row)).rev, true) = b :=
  pairOrbitMap_anchor_right P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward)

theorem anchor_predecessor (hanchor : b = P.edge a) :
    f (.inr (0 : Fin (length o.row)).rev, false) = P.face a := by
  exact (pairOrbitMap_anchor_predecessor P.rotation a
    (forwardPeriod G length rows L a o hforward) b
    (backwardPeriod G length rows L b o hbackward)).trans (by rw [hanchor]; rfl)

theorem range (d : D) :
    d ∈ Set.range f ↔ P.rotation.SameCycle a d ∨ P.rotation.SameCycle b d :=
  pairOrbitMap_range P.rotation a (forwardPeriod G length rows L a o hforward)
    b (backwardPeriod G length rows L b o hbackward) d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MatchedPair
