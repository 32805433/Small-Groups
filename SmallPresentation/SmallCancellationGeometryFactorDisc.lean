module

public import SmallPresentation.SmallCancellationGeometryMarkedFactor

/-!
# Normalizing an old factor disc

A factor disc has a constant marker tag, alternating marker signs, trivial negative
corners, and total coefficient product one. A negative-positive marker pair is always
available. Its actual cancellation preserves these properties on every surviving part
of that vertex. Region equations are handled separately, including component splitting.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

open PermutationCycles

variable {D X H : Type*} [Group H] {P : RibbonMap D}

/-- The exact local word properties of an old factor relation after augmentation. -/
structure FactorDisc (L : RibbonLabelling P X H) (a : D) : Prop where
  tag : ∀ d, P.rotation.SameCycle a d → (L.arc d).1 = (L.arc a).1
  alternating : ∀ d, P.rotation.SameCycle a d →
    (L.arc (P.rotation d)).2 = !((L.arc d).2)
  negative : ∀ d, P.rotation.SameCycle a d → (L.arc d).2 = false → L.corner d = 1
  product : ((P.vertexBoundary a).map L.corner).prod = 1

namespace FactorDisc

variable {L : RibbonLabelling P X H} {a : D} (F : FactorDisc L a)

include F in
/-- The underlying alternating factor shape, forgetting the relation equation. -/
theorem toFactorVertexShape : FactorVertexShape L a :=
  ⟨F.tag, F.alternating, F.negative⟩

include F in
/-- Every nonempty factor disc contains a negative marker, even if its marked start is positive. -/
theorem exists_negative : ∃ d, P.rotation.SameCycle a d ∧ (L.arc d).2 = false :=
  F.toFactorVertexShape.exists_negative

/-- A negative marker and its successor are a genuine cancellable adjacent pair. -/
def cancellation (d : D) (hd : P.rotation.SameCycle a d) (hs : (L.arc d).2 = false) :
    AdjacentCancellation P := F.toFactorVertexShape.cancellation d hd hs

theorem cancellation_arc (d : D) (hd : P.rotation.SameCycle a d) (hs : (L.arc d).2 = false) :
    L.arc (F.cancellation d hd hs).right = reverseLetter (L.arc (F.cancellation d hd hs).left) :=
  F.toFactorVertexShape.cancellation_arc d hd hs

theorem cancellation_corner (d : D) (hd : P.rotation.SameCycle a d)
    (hs : (L.arc d).2 = false) : L.corner (F.cancellation d hd hs).left = 1 :=
  F.negative d hd hs

variable [Finite D]

include F in
/-- The factor-disc conditions are independent of the chosen incidence on its vertex. -/
theorem rebase (d : D) (hd : P.rotation.SameCycle a d) : FactorDisc L d where
  tag e he := (F.tag e (hd.trans he)).trans (F.tag d hd).symm
  alternating e he := F.alternating e (hd.trans he)
  negative e he hs := F.negative e (hd.trans he) hs
  product := (cycleProduct_eq_one_of_sameCycle P.rotation L.corner hd).mp F.product

include F in
theorem product_at (d : D) (hd : P.rotation.SameCycle a d) :
    ((P.vertexBoundary d).map L.corner).prod = 1 :=
  (cycleProduct_eq_one_of_sameCycle P.rotation L.corner hd).mp F.product

/-- Cancelling a chosen negative-positive pair retains the local factor-disc normal form. -/
theorem cancel (d : D) (hd : P.rotation.SameCycle a d) (hs : (L.arc d).2 = false)
    (e : (F.cancellation d hd hs).Dart) (he : P.rotation.SameCycle a e.val) :
    FactorDisc ((F.cancellation d hd hs).labelling L (F.cancellation_arc d hd hs)) e := by
  have shape := F.toFactorVertexShape.cancel d hd hs e he
  refine ⟨shape.tag, shape.alternating, shape.negative, ?_⟩
  exact (F.toFactorVertexShape.cancel_vertex_product d hd hs e).trans (F.product_at e.val he)

end FactorDisc
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
