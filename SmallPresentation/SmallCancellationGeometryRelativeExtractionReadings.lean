module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionSystem

/-!
# Exact indexed readings on the new vertices of a mixed picture

Origins are required only on new vertices, so empty row-index types remain allowed.
Actual cancellation and restriction transport these readings without choosing new row
representatives or discarding the based cyclic start.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type*} [Finite D] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)}

/-- Complete readings on new vertices of a picture that may also contain old factor discs. -/
structure MixedReadings (S : OldDiscSystem L) where
  origin : {d // ¬ S.old d} → Origin length
  forward : ∀ (d : D) (hd : ¬ S.old d), (L.arc d).2 = true →
    L.vertexWord d = Augmentation.word G length rows (origin ⟨d, hd⟩)
  backward : ∀ (d : D) (hd : ¬ S.old d), (L.arc d).2 = false →
    L.reverseVertexWord d = Augmentation.word G length rows (origin ⟨d, hd⟩)

namespace MixedReadings

variable {S : OldDiscSystem L} (R : MixedReadings (rows := rows) S)

/-- Cancellation retains exactly the origin of each original new incidence. -/
noncomputable def cancel (d : D) (hd : S.old d) (hs : (L.arc d).2 = false) :
    MixedReadings (rows := rows) (S.cancel d hd hs) where
  origin e := R.origin ⟨e.val.val, e.property⟩
  forward e he ha := by
    rw [S.cancel_new_vertexWord d hd hs e he]
    exact R.forward e.val he ha
  backward e he ha := by
    rw [S.cancel_new_reverseVertexWord d hd hs e he]
    exact R.backward e.val he ha

/-- A component restriction retains the same original incidence labels and readings. -/
noncomputable def restrict (p : D → Prop)
    (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d) :
    MixedReadings (rows := rows) (S.restrict p he hr) where
  origin d := R.origin ⟨d.val.val, d.property⟩
  forward d hd ha := by
    rw [L.restrict_vertexWord p he hr]
    exact R.forward d.val hd ha
  backward d hd ha := by
    rw [L.restrict_reverseVertexWord p he hr]
    exact R.backward d.val hd ha

/-- Once every old vertex has been removed, the inherited readings are precisely the
all-new data required by the metric dipole theorem. -/
noncomputable def augmented (hnew : ∀ d, ¬ S.old d) : AugmentedReadings G length rows P L where
  origin d := R.origin ⟨d, hnew d⟩
  forward d hd := R.forward d (hnew d) hd
  backward d hd := R.backward d (hnew d) hd

end MixedReadings
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
