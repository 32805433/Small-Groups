module

public import SmallPresentation.SmallCancellationGeometryMarkedPictureRestriction
public import SmallPresentation.SmallCancellationGeometryFactorCornerCancellation

/-!
# Actual old-corner cancellation in marked pictures

The marked vertex and all remaining attaching words are retained literally. Whenever
its marked component has valid region equations, the result is a smaller marked picture.
The exceptional-face case is deliberately left to the separate capping argument.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] (T : MarkedRelativePicture G length rows D)
    (d : D) (hd : T.oldDiscs.old d) (hs : (T.labels.arc d).2 = false)

attribute [local instance] Classical.propDecidable

abbrev oldCut := T.oldDiscs.cancellation d hd hs

abbrev oldCutMarked : (T.oldCut d hd hs).Dart :=
  T.oldDiscs.survivingNew d hd hs T.marked T.marked_not_old

/-- Exact original indexed readings survive cancellation at an old factor disc. -/
noncomputable def oldCutReadings : MarkedMixedReadings G length rows
    (T.oldDiscs.cancel d hd hs) (T.oldCutMarked d hd hs) where
  origin e := T.readings.origin ⟨e.val.val, e.property.1,
    fun h ↦ e.property.2 (((T.oldCut d hd hs).sameVertex_iff _ _).mpr h)⟩
  forward e he ha := by
    rw [T.oldDiscs.cancel_new_vertexWord d hd hs e he.1]
    exact T.readings.forward e.val ⟨he.1,
      fun h ↦ he.2 (((T.oldCut d hd hs).sameVertex_iff _ _).mpr h)⟩ ha
  backward e he ha := by
    rw [T.oldDiscs.cancel_new_reverseVertexWord d hd hs e he.1]
    exact T.readings.backward e.val ⟨he.1,
      fun h ↦ he.2 (((T.oldCut d hd hs).sameVertex_iff _ _).mpr h)⟩ ha

/-- The marked vertex is untouched even when the surrounding edge reconnection separates components. -/
theorem oldCutShape : FactorVertexShape
    ((T.oldCut d hd hs).labelling T.labels (T.oldDiscs.cancellation_arc d hd hs))
    (T.oldCutMarked d hd hs) := by
  have oldCycle (e : (T.oldCut d hd hs).Dart)
      (he : (T.oldCut d hd hs).delete.rotation.SameCycle (T.oldCutMarked d hd hs) e) :
      T.map.rotation.SameCycle T.marked e.val :=
    ((T.oldCut d hd hs).sameVertex_iff _ _).mp he
  have new (e : (T.oldCut d hd hs).Dart)
      (he : (T.oldCut d hd hs).delete.rotation.SameCycle (T.oldCutMarked d hd hs) e) :
      ¬T.oldDiscs.old e.val :=
    fun ho ↦ T.marked_not_old ((T.oldDiscs.constant (oldCycle e he)).mpr ho)
  constructor
  · intro e he
    exact T.shape.tag e.val (oldCycle e he)
  · intro e he
    change (T.labels.arc ((T.oldCut d hd hs).delete.rotation e).val).2 = _
    rw [T.oldDiscs.cancel_new_rotation d hd hs e (new e he)]
    exact T.shape.alternating e.val (oldCycle e he)
  · intro e he hn
    rw [T.oldDiscs.cancel_new_corner d hd hs e (new e he)]
    exact T.shape.negative e.val (oldCycle e he) hn

/-- The original marked coefficient product survives exactly. -/
theorem oldCutProduct :
    (((T.oldCut d hd hs).delete.vertexBoundary (T.oldCutMarked d hd hs)).map
      ((T.oldCut d hd hs).labelling T.labels (T.oldDiscs.cancellation_arc d hd hs)).corner).prod =
      ((T.map.vertexBoundary T.marked).map T.labels.corner).prod := by
  have hh := (T.oldCut d hd hs).vertex_value T.labels
    (T.oldDiscs.cancellation_arc d hd hs) (T.oldDiscs.cancellation_corner d hd hs)
    (fun _ ↦ (1 : Monoid.CoprodI G)) (fun _ ↦ (inv_one).symm)
    (MonoidHom.id _) (T.oldCutMarked d hd hs)
  simpa only [MonoidHom.id_apply, one_mul, oldCutMarked, OldDiscSystem.survivingNew] using hh

/-- Actual marked component after an old-corner cut, with region validity explicit. -/
noncomputable def oldCutPicture
    (hfaces : ∀ e, (T.oldCut d hd hs).delete.SameComponent (T.oldCutMarked d hd hs) e →
      ((T.oldCut d hd hs).labelling T.labels (T.oldDiscs.cancellation_arc d hd hs)).faceValue e = 1) :
    MarkedRelativePicture G length rows
      {e : (T.oldCut d hd hs).Dart //
        (T.oldCut d hd hs).delete.SameComponent (T.oldCutMarked d hd hs) e} :=
  ofComponent (T.oldDiscs.cancel d hd hs) (T.oldCutMarked d hd hs) T.marked_not_old
    (by
      have hh := congrArg List.length ((T.oldCut d hd hs).vertexBoundary_unchanged
        (T.oldCutMarked d hd hs) (T.oldDiscs.new_other_vertex d hd T.marked T.marked_not_old))
      simpa only [List.length_map, oldCutMarked, OldDiscSystem.survivingNew, T.marked_size] using hh)
    (T.oldCutShape d hd hs) (fun h ↦ T.nontrivial ((T.oldCutProduct d hd hs).symm.trans h))
    (T.oldCutReadings d hd hs)
    (T.factorCorners.cancel (T.oldCut d hd hs) (T.oldDiscs.cancellation_arc d hd hs) hs)
    ((T.oldCut d hd hs).delete_euler T.euler) hfaces

variable (hfaces : ∀ e, (T.oldCut d hd hs).delete.SameComponent (T.oldCutMarked d hd hs) e →
  ((T.oldCut d hd hs).labelling T.labels (T.oldDiscs.cancellation_arc d hd hs)).faceValue e = 1)

/-- The induced attaching-incidence map is the literal original dart inclusion. -/
def oldCutNew (e : {e // (T.oldCutPicture d hd hs hfaces).IsNew e}) : {d // T.IsNew d} := by
  refine ⟨e.val.val.val, e.property.1, ?_⟩
  intro h
  apply e.property.2
  apply ((T.oldCut d hd hs).delete.restrict_sameVertex_iff _ _ _ _ _).mpr
  exact ((T.oldCut d hd hs).sameVertex_iff _ _).mpr h

theorem oldCutNew_cycles (e f : {e // (T.oldCutPicture d hd hs hfaces).IsNew e}) :
    (T.oldCutPicture d hd hs hfaces).map.rotation.SameCycle e.val f.val ↔
      T.map.rotation.SameCycle (T.oldCutNew d hd hs hfaces e).val
        (T.oldCutNew d hd hs hfaces f).val :=
  ((T.oldCut d hd hs).delete.restrict_sameVertex_iff _ _ _ e.val f.val).trans
    ((T.oldCut d hd hs).sameVertex_iff e.val.val f.val.val)

/-- Passing to the marked component cannot add attaching vertices. -/
theorem oldCutPicture_count : (T.oldCutPicture d hd hs hfaces).newCount ≤ T.newCount :=
  T.newCount_le_of_cycle_embedding (T.oldCutPicture d hd hs hfaces)
    (T.oldCutNew d hd hs hfaces) (T.oldCutNew_cycles d hd hs hfaces)

/-- At least the actual cancelled pair is lost, independent of subsequent component selection. -/
theorem oldCutPicture_darts : Fintype.card {e : (T.oldCut d hd hs).Dart //
    (T.oldCut d hd hs).delete.SameComponent (T.oldCutMarked d hd hs) e} < Fintype.card D :=
  lt_of_le_of_lt (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
    (T.oldCut d hd hs).card_darts_lt

include d hd hs hfaces in
/-- Validity of the cut marked component contradicts lexicographic minimality. -/
theorem Minimal.oldCut_impossible (hmin : T.Minimal) : False := by
  exact Minimal.not_fewer_darts_of_rows_le T hmin (T.oldCutPicture d hd hs hfaces)
    (T.oldCutPicture_count d hd hs hfaces) (T.oldCutPicture_darts d hd hs)

include hd hs in
/-- In particular, a two-marker old relation can never occur in a minimal marked picture. -/
theorem Minimal.no_terminal_old (hmin : T.Minimal)
    (ht : T.map.rotation (T.map.rotation d) = d) : False := by
  apply Minimal.oldCut_impossible T d hd hs ?_ hmin
  intro e _
  rw [(T.oldCut d hd hs).delete_faceValue_of_two_cycle T.labels
    (T.oldDiscs.cancellation_arc d hd hs) ht
    (T.oldDiscs.cancellation_corner d hd hs) (T.oldDiscs.disc d hd).product e]
  exact T.faces e.val

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture
