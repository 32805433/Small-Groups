module

public import SmallPresentation.SmallCancellationGeometryMarkedOldCancellation
public import SmallPresentation.SmallCancellationGeometryFaceCapPicture
public import SmallPresentation.SmallCancellationGeometryCornerCancellationValidFaces

/-!
# Excluding defective components separated from the marked boundary

Cap the sole exceptional region of a separated component. The two new cap darts replace
the two cancelled darts, while the discarded original marked component makes the total
strictly smaller. Attaching vertices inject into the original actual vertex quotient.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] (T : MarkedRelativePicture G length rows D)
    (d : D) (hd : T.oldDiscs.old d) (hs : (T.labels.arc d).2 = false)

attribute [local instance] Classical.propDecidable

variable (x : (T.oldCut d hd hs).Dart)
    (haway : ¬(T.oldCut d hd hs).delete.SameComponent (T.oldCutMarked d hd hs) x)

abbrev AwayDart := {e : (T.oldCut d hd hs).Dart // (T.oldCut d hd hs).delete.SameComponent x e}

noncomputable abbrev awayMap := (T.oldCut d hd hs).delete.componentRibbon x

noncomputable abbrev awayLabels :=
  ((T.oldCut d hd hs).labelling T.labels (T.oldDiscs.cancellation_arc d hd hs)).restrict
    ((T.oldCut d hd hs).delete.SameComponent x)
    ((T.oldCut d hd hs).delete.component_membership_edge x)
    ((T.oldCut d hd hs).delete.component_membership_rotation x)

noncomputable abbrev awayOld := (T.oldDiscs.cancel d hd hs).restrict
  ((T.oldCut d hd hs).delete.SameComponent x)
  ((T.oldCut d hd hs).delete.component_membership_edge x)
  ((T.oldCut d hd hs).delete.component_membership_rotation x)

include haway in
/-- The old marked vertex has no incidence in the separated component. -/
theorem away_not_marked (e : T.AwayDart d hd hs x) :
    ¬(T.oldCut d hd hs).delete.rotation.SameCycle (T.oldCutMarked d hd hs) e.val := by
  intro hm
  exact haway (Relation.EqvGen.trans _ _ _
    ((T.oldCut d hd hs).delete.component_of_vertexCycle hm) e.property.symm)

/-- Every nonold vertex on the separated component is an original attaching row. -/
noncomputable def awayReadings : MixedReadings (rows := rows) (T.awayOld d hd hs x) where
  origin e := (T.oldCutReadings d hd hs).origin
    ⟨e.val.val, e.property, T.away_not_marked d hd hs x haway e.val⟩
  forward e he ha := by
    rw [RibbonLabelling.restrict_vertexWord]
    exact (T.oldCutReadings d hd hs).forward e.val
      ⟨he, T.away_not_marked d hd hs x haway e⟩ ha
  backward e he ha := by
    rw [RibbonLabelling.restrict_reverseVertexWord]
    exact (T.oldCutReadings d hd hs).backward e.val
      ⟨he, T.away_not_marked d hd hs x haway e⟩ ha

variable
    (hregions : ∀ e, (T.oldCut d hd hs).delete.SameComponent x e →
      ¬(T.oldCut d hd hs).delete.face.SameCycle x e →
      ((T.oldCut d hd hs).labelling T.labels (T.oldDiscs.cancellation_arc d hd hs)).faceValue e = 1)
    (hbad : ((T.oldCut d hd hs).labelling T.labels
      (T.oldDiscs.cancellation_arc d hd hs)).faceValue x ≠ 1)

/-- The actual face cap on the separated component is a marked counterexample. -/
noncomputable def awayPicture : MarkedRelativePicture G length rows (T.AwayDart d hd hs x ⊕ Bool) :=
  FaceCap.pictureAt G length rows (T.awayMap d hd hs x) (T.awayLabels d hd hs x)
    (T.awayOld d hd hs x) (T.awayReadings d hd hs x haway)
    ((T.factorCorners.cancel (T.oldCut d hd hs) (T.oldDiscs.cancellation_arc d hd hs) hs).restrict _ _ _)
    ((T.oldCut d hd hs).delete.componentRibbon_connected x)
    ((T.oldCut d hd hs).delete.restrict_euler _ _ _ ((T.oldCut d hd hs).delete_euler T.euler))
    ⟨x, Relation.EqvGen.refl _⟩
    (by
      intro e he
      exact (RibbonLabelling.restrict_faceValue _ _ _ _ e).trans
        (hregions e.val e.property
          (fun hh ↦ he (((T.oldCut d hd hs).delete.restrict_sameFace_iff _ _ _ _ _).mpr hh))))
    (by
      intro hh
      exact hbad ((RibbonLabelling.restrict_faceValue _ _ _ _
        ⟨x, Relation.EqvGen.refl _⟩).symm.trans hh))

/-- The cap's new incidences map to genuine original attaching incidences. -/
noncomputable def awayNew
    (e : {e // (T.awayPicture d hd hs x haway hregions hbad).IsNew e}) : {e // T.IsNew e} := by
  let a := (T.awayMap d hd hs x).face.symm ⟨x, Relation.EqvGen.refl _⟩
  let u := FaceCap.newOriginal G (T.awayMap d hd hs x) a (T.awayLabels d hd hs x)
    (T.awayOld d hd hs x) ((T.awayLabels d hd hs x).faceValue ((T.awayMap d hd hs x).face a)) e
  refine ⟨u.val.val.val, u.property, ?_⟩
  intro hm
  exact T.away_not_marked d hd hs x haway u.val
    (((T.oldCut d hd hs).sameVertex_iff _ _).mpr hm)

/-- The map on cap incidences reflects vertex cycles through both actual inclusions. -/
theorem awayNew_cycles
    (e f : {e // (T.awayPicture d hd hs x haway hregions hbad).IsNew e}) :
    (T.awayPicture d hd hs x haway hregions hbad).map.rotation.SameCycle e.val f.val ↔
      T.map.rotation.SameCycle (T.awayNew d hd hs x haway hregions hbad e).val
        (T.awayNew d hd hs x haway hregions hbad f).val := by
  let a := (T.awayMap d hd hs x).face.symm ⟨x, Relation.EqvGen.refl _⟩
  exact (FaceCap.newOriginal_sameCycle G (T.awayMap d hd hs x) a (T.awayLabels d hd hs x)
    (T.awayOld d hd hs x) _ e f).trans
    (((T.oldCut d hd hs).delete.restrict_sameVertex_iff _ _ _ _ _).trans
      ((T.oldCut d hd hs).sameVertex_iff _ _))

/-- Capping does not add attaching rows. -/
theorem awayPicture_count : (T.awayPicture d hd hs x haway hregions hbad).newCount ≤ T.newCount :=
  T.newCount_le_of_cycle_embedding (T.awayPicture d hd hs x haway hregions hbad)
    (T.awayNew d hd hs x haway hregions hbad) (T.awayNew_cycles d hd hs x haway hregions hbad)

include haway in
/-- The new cap restores two cancelled darts, but the omitted marked component is nonempty. -/
theorem awayPicture_darts : Fintype.card (T.AwayDart d hd hs x ⊕ Bool) < Fintype.card D := by
  have hlt : Fintype.card (T.AwayDart d hd hs x) < Fintype.card (T.oldCut d hd hs).Dart := by
    apply Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
      (b := T.oldCutMarked d hd hs)
    rintro ⟨e, he⟩
    have hh := e.property
    rw [he] at hh
    exact haway hh.symm
  have hc := (T.oldCut d hd hs).card_darts
  simp only [Fintype.card_sum, Fintype.card_bool]
  omega

include haway hregions hbad in
/-- A minimal marked picture has no defective one-exception component separated by
an old-corner cut. The argument uses no quotient-potential or factor-injectivity claim. -/
theorem Minimal.no_away_defect (hmin : T.Minimal) : False := by
  exact Minimal.not_fewer_darts_of_rows_le T hmin (T.awayPicture d hd hs x haway hregions hbad)
    (T.awayPicture_count d hd hs x haway hregions hbad) (T.awayPicture_darts d hd hs x haway)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture
