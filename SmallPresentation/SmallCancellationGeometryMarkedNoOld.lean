module

public import SmallPresentation.SmallCancellationGeometryMarkedOldCap

/-!
# A minimal marked counterexample contains no old factor discs

All actual cancellation cases are covered. In the splitting case, capping the component
away from the original marked boundary excludes its defect by lexicographic minimality;
the exact cut-product relation then restores the other face as well.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] (T : MarkedRelativePicture G length rows D)
    (hmin : T.Minimal)

include hmin in
/-- A negative marker of an old disc gives a strictly smaller marked counterexample. -/
theorem Minimal.no_old_negative (d : D) (hd : T.oldDiscs.old d)
    (hs : (T.labels.arc d).2 = false) : False := by
  classical
  let C := T.oldCut d hd hs
  let M := C.labelling T.labels (T.oldDiscs.cancellation_arc d hd hs)
  have harc := T.oldDiscs.cancellation_arc d hd hs
  have hleft := T.oldDiscs.cancellation_corner d hd hs
  by_cases ht : T.map.rotation C.right = C.left
  · exact Minimal.no_terminal_old T d hd hs hmin ht
  apply Minimal.oldCut_impossible T d hd hs ?_ hmin
  intro e _
  by_cases hl : T.map.edge C.left = C.right
  · exact C.all_faces_of_loop T.labels harc hleft T.faces ht hl e
  by_cases hf : T.map.face.SameCycle C.predecessor C.right
  · let a := C.beforeDart ht
    let b := C.mateDart hl
    have hsep : ¬C.delete.SameComponent a b := C.delete_regions_separated ht hl T.euler hf
    have hre : M.faceValue a = 1 ↔ M.faceValue b = 1 :=
      C.split_faces_equivalent T.labels harc hleft T.faces ht hl hf
    have away_valid (x y : C.Dart) (hxy : ¬C.delete.SameComponent x y)
        (haway : ¬C.delete.SameComponent (T.oldCutMarked d hd hs) x)
        (hpair : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) : M.faceValue x = 1 := by
      by_contra hv
      apply Minimal.no_away_defect T d hd hs x haway ?_ hv hmin
      intro z hz hface
      have hy : ¬C.delete.face.SameCycle y z := by
        intro hh
        exact hxy (Relation.EqvGen.trans _ _ _ hz (C.delete.component_of_faceCycle hh).symm)
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact C.faces_outside_split T.labels harc hleft T.faces ht hl z hface hy
      · exact C.faces_outside_split T.labels harc hleft T.faces ht hl z hy hface
    have hab : M.faceValue a = 1 ∧ M.faceValue b = 1 := by
      by_cases hm : C.delete.SameComponent (T.oldCutMarked d hd hs) a
      · have hn : ¬C.delete.SameComponent (T.oldCutMarked d hd hs) b := by
          intro hb
          exact hsep (Relation.EqvGen.trans _ _ _ hm.symm hb)
        have hb := away_valid b a (fun h ↦ hsep h.symm) hn (Or.inr ⟨rfl, rfl⟩)
        exact ⟨hre.mpr hb, hb⟩
      · have ha := away_valid a b hsep hm (Or.inl ⟨rfl, rfl⟩)
        exact ⟨ha, hre.mp ha⟩
    rcases C.delete_face_classification ht hl e with h | h | h
    · rw [C.delete_unaffected_face T.labels harc hleft ht e h.1 h.2]
      exact T.faces e.val
    · exact (M.faceValue_eq_one_of_sameCycle h).mpr hab.1
    · exact (M.faceValue_eq_one_of_sameCycle h).mpr hab.2
  · exact C.all_faces_of_merge T.labels harc hleft T.faces ht hf e

include hmin in
/-- Every vertex of a minimal marked picture is either the marked boundary or an actual
indexed attaching row. Old factor relations have been excluded by concrete surgery. -/
theorem Minimal.no_old (d : D) : ¬T.oldDiscs.old d := by
  intro hd
  obtain ⟨e, he, hs⟩ := (T.oldDiscs.disc d hd).exists_negative
  exact Minimal.no_old_negative T hmin e ((T.oldDiscs.constant he).mp hd) hs

/-- Complete original indexed readings away from the marked boundary, now with no old discs. -/
noncomputable def Minimal.readingsExcept :
    AugmentedReadingsExcept G length rows T.map T.labels T.marked := by
  classical
  let a := Classical.choose T.exists_new
  have ha : T.IsNew a := Classical.choose_spec T.exists_new
  exact {
    origin := fun d ↦ if hm : T.map.rotation.SameCycle T.marked d
      then T.readings.origin ⟨a, ha⟩
      else T.readings.origin ⟨d, Minimal.no_old T hmin d, hm⟩
    forward := by
      intro d hm hs
      simp only [dite_eq_right hm]
      exact T.readings.forward d ⟨Minimal.no_old T hmin d, hm⟩ hs
    backward := by
      intro d hm hs
      simp only [dite_eq_right hm]
      exact T.readings.backward d ⟨Minimal.no_old T hmin d, hm⟩ hs }

/-- The metric curvature theorem now applies to the actual minimal marked picture. -/
theorem Minimal.matched_origin
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    ∃ y, ¬T.map.rotation.SameCycle T.marked y ∧ (T.labels.arc y).2 = true ∧
      ¬T.map.rotation.SameCycle T.marked (T.map.edge y) ∧
      (Minimal.readingsExcept T hmin).origin (T.map.edge y) =
        (Minimal.readingsExcept T hmin).origin y := by
  obtain ⟨a, ha⟩ := T.exists_new
  apply (Minimal.readingsExcept T hmin).exists_matched_origin_of_rows
    hidentity hreduced hmetric (T.marked_size.le) T.marked a ha.2 T.connected
    (fun d _ ↦ T.faces d)
  have hh := T.euler
  have hc := T.map.card_components_of_connected T.connected T.marked
  simpa only [RibbonMap.EulerEquality, hc, mul_one] using hh

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture
