module

public import SmallPresentation.SmallCancellationGeometryCornerCancellation

/-! Adjacent corner cancellation strictly decreases the finite incidence set. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

attribute [local instance] Classical.propDecidable

variable {D : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

theorem card_darts [Fintype D] : Fintype.card D = Fintype.card C.Dart + 2 := by
  classical
  let p := fun d : D ↦ d = C.left ∨ d = C.right
  have hc := Fintype.card_congr (Equiv.sumCompl p)
  simp only [Fintype.card_sum] at hc
  have hp : Fintype.card {d : D // p d} = 2 :=
    Fintype.card_subtype_eq_or_eq_of_ne C.ne
  have he : {d : D // ¬p d} ≃ C.Dart := Equiv.subtypeEquivRight (fun _ ↦ not_or)
  have hd := Fintype.card_congr he
  omega

theorem card_darts_lt [Fintype D] : Fintype.card C.Dart < Fintype.card D := by
  rw [C.card_darts]
  omega

/-- Reconnecting the two incident edges reduces the actual edge count by one. -/
theorem card_edges [Fintype D] : Fintype.card P.Edge = Fintype.card C.delete.Edge + 1 := by
  have hd := C.card_darts
  have ho := P.card_darts
  have hn := C.delete.card_darts
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
