module

public import SmallPresentation.SmallCancellationDipolePairMatchedCoordinates
public import SmallPresentation.SmallCancellationDipolePairFactorReplacement

/-! A matched pair of actual row readings supplies the complete noncircular surgery data. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MatchedPair

variable {A I : Type} (G : A → Type) [∀ x, Group (G x)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    {D : Type*} [Finite D] {P : RibbonMap D} (L : RibbonLabelling P A (Monoid.CoprodI G))
    (a b : D) (o : Origin length)
    (hforward : L.vertexWord a = Augmentation.word G length rows o)
    (hbackward : L.reverseVertexWord b = Augmentation.word G length rows o)
    (hnegative : (L.arc b).2 = false) (hmetric : MetricSmallCancellation G length rows)
    (C : RibbonLabelling.FactorCorners G L) (hedge : b = P.edge a)

local notation "f" => embedding G length rows L a b o hforward hbackward hnegative hmetric
local notation "ff" => first_false G length rows L a b o hforward hbackward hnegative hmetric
local notation "ft" => first_true G length rows L a b o hforward hbackward hnegative hmetric
local notation "sf" => second_false G length rows L a b o hforward hbackward hnegative hmetric
local notation "st" => second_true G length rows L a b o hforward hbackward hnegative hmetric

/-- Complete actual surgery data obtained from literal opposite indexed attaching readings.
No quotient homomorphism or injectivity hypothesis occurs in this construction. -/
noncomputable def replacement : PairFactorBlocks.ReplacementData P L (length o.row) where
  anchor := 0
  embedding := f
  rotation d := (rotation G length rows L a b o hforward hbackward hnegative hmetric d).symm
  edge := by
    rw [anchor_first, anchor_second]
    exact hedge.symm
  tag k := (syllableAt G length rows o k.val).1
  coeff k := includeSyllable G (syllableAt G length rows o k.val)
  arc := PairFactorBlocks.paired_arc G length rows L o a b hforward hbackward f ff ft sf st
  corner := PairFactorBlocks.paired_corner G length rows L o a b hforward hbackward C f ff ft sf st

local notation "T" => replacement G length rows L a b o hforward hbackward hnegative hmetric C hedge

/-- The surgery anchor is precisely the given original positive dart. -/
theorem replacement_point : (T).point = a :=
  anchor_first G length rows L a b o hforward hbackward hnegative hmetric

/-- Exactly the two original attaching vertices are reclassified as factor discs. -/
theorem replacement_range (d : D) :
    d ∈ Set.range (T).embedding ↔ P.rotation.SameCycle a d ∨ P.rotation.SameCycle b d :=
  range G length rows L a b o hforward hbackward hnegative hmetric d

/-- The actual anchor splice merges two distinct original attaching vertices. -/
theorem replacement_distinct : ¬P.rotation.SameCycle (T).point (P.edge (T).point) := by
  rw [replacement_point, ← hedge]
  exact matched_readings_distinct_vertices G length rows P L hmetric a b o
    hforward hbackward hnegative

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MatchedPair
