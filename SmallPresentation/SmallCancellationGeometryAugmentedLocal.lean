module

public import SmallPresentation.SmallCancellationDipoleAugmentedReadings
public import SmallPresentation.SmallCancellationGeometryVertexTransport

/-! Complete augmented readings from local vertex coordinates inside a mixed picture. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool)

/-- A local row-coordinate ribbon. Its edge pairing is only used to instantiate the reading
API; embeddings below require preservation of the vertex rotation and the labels. -/
def localRibbon : RibbonMap (Darts length labels) where
  edge :=
    { toFun := fun d ↦ ⟨d.1, d.2.1, !d.2.2⟩
      invFun := fun d ↦ ⟨d.1, d.2.1, !d.2.2⟩
      left_inv := by rintro ⟨o, k, b⟩; simp
      right_inv := by rintro ⟨o, k, b⟩; simp }
  edge_involutive := by rintro ⟨o, k, b⟩; simp
  edge_ne := by
    rintro ⟨o, k, b⟩ h
    have hh := congrArg (fun d : Darts length labels ↦ d.2.2) h
    cases b <;> cases hh
  rotation := rotation length labels

theorem localRibbon_edge_arc (d : Darts length labels) :
    arc length G rows labels signs ((localRibbon length labels).edge d) =
      reverseLetter (arc length G rows labels signs d) := by
  rcases d with ⟨o, k, b⟩
  cases b <;> rfl

variable {D : Type*} {P : RibbonMap D} (L : RibbonLabelling P A (Monoid.CoprodI G))
    (f : Darts length labels → D) (hinj : Function.Injective f)
    (hrot : ∀ d, f (rotation length labels d) = P.rotation (f d))
    (harc : ∀ d, L.arc (f d) = arc length G rows labels signs d)
    (hcorner : ∀ d, L.corner (f d) = corner length G rows labels signs d)

include hinj hrot harc hcorner in
/-- Literal local coordinates prove the complete forward reading inside an arbitrary picture. -/
theorem forward_of_coordinates [Finite O] (o : O) (k : Fin (length (labels o))) :
    L.vertexWord (f ⟨o, k, false⟩) =
      Augmentation.word G length rows (positiveOrigin length (labels o) (signs o) k) := by
  let M := labelling length G rows labels signs (localRibbon length labels)
    (localRibbon_edge_arc length G rows labels signs)
  rw [M.vertexWord_map L f hinj hrot harc hcorner]
  exact positive_vertexWord length G rows labels signs (localRibbon length labels)
    (localRibbon_edge_arc length G rows labels signs) rfl o k

include hinj hrot harc hcorner in
/-- The same coordinates prove the full backwards reading at the trailing marker. -/
theorem backward_of_coordinates [Finite O] (o : O) (k : Fin (length (labels o))) :
    L.reverseVertexWord (f ⟨o, k, true⟩) =
      Augmentation.word G length rows (negativeOrigin length (labels o) (signs o) k) := by
  let M := labelling length G rows labels signs (localRibbon length labels)
    (localRibbon_edge_arc length G rows labels signs)
  rw [M.reverseVertexWord_map L f hinj hrot harc hcorner]
  exact negative_vertexWord length G rows labels signs (localRibbon length labels)
    (localRibbon_edge_arc length G rows labels signs) rfl o k

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
