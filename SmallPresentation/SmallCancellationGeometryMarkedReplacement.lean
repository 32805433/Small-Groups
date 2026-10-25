module

public import SmallPresentation.SmallCancellationGeometryMarkedNoOld
public import SmallPresentation.SmallCancellationDipoleRelativeRetainedWords

/-!
# Replacing selected attaching vertices by actual factor relations

This wrapper retains the original marked component and compares the actual attaching
vertex quotients. Its geometric inputs are explicit map, labels and factor discs supplied
by surgery; neither quotient injectivity nor a reduction theorem is assumed.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] (T : MarkedRelativePicture G length rows D)
    (Q : RibbonMap D) (M : RibbonLabelling Q A (Monoid.CoprodI G)) (S : OldDiscSystem M)
    (selected : D → Prop) (hinv : ∀ e, selected (T.map.rotation e) ↔ selected e)
    (hmark : ¬selected T.marked) (hold : ∀ e, S.old e ↔ T.oldDiscs.old e ∨ selected e)
    (hrot : ∀ e, ¬selected e → Q.rotation e = T.map.rotation e)
    (harc : ∀ e, ¬selected e → M.arc e = T.labels.arc e)
    (hcorner : ∀ e, ¬selected e → M.corner e = T.labels.corner e)

attribute [local instance] Classical.propDecidable

include hinv in
/-- Every incidence on an unselected original vertex is unselected. -/
theorem outside_selected {e : D} (he : ¬selected e) {f : D}
    (hf : T.map.rotation.SameCycle e f) : ¬selected f :=
  fun hs ↦ he ((T.map.vertex_predicate_constant selected hinv hf).mpr hs)

include hinv hrot in
/-- Unselected vertices keep exactly their old cycles. -/
theorem replacement_sameCycle (e : D) (he : ¬selected e) (f : D) :
    Q.rotation.SameCycle e f ↔ T.map.rotation.SameCycle e f :=
  RibbonLabelling.retained_sameCycle e
    (fun z hz ↦ hrot z (outside_selected T selected hinv he hz)) f

/-- New vertices retain their complete original indexed readings after reclassification. -/
noncomputable def replacementReadings : MarkedMixedReadings G length rows S T.marked where
  origin e := T.readings.origin ⟨e.val,
    fun ho ↦ e.property.1 ((hold e.val).mpr (Or.inl ho)),
    fun hm ↦ e.property.2 ((replacement_sameCycle T Q selected hinv hrot T.marked hmark e.val).mpr hm)⟩
  forward e he hs := by
    have hn : ¬selected e := fun hh ↦ he.1 ((hold e).mpr (Or.inr hh))
    rw [RibbonLabelling.retained_vertexWord T.labels e M
      (fun z hz ↦ hrot z (outside_selected T selected hinv hn hz))
      (fun z hz ↦ harc z (outside_selected T selected hinv hn hz))
      (fun z hz ↦ hcorner z (outside_selected T selected hinv hn hz))]
    exact T.readings.forward e ⟨fun ho ↦ he.1 ((hold e).mpr (Or.inl ho)),
      fun hm ↦ he.2 ((replacement_sameCycle T Q selected hinv hrot T.marked hmark e).mpr hm)⟩
      (by rwa [harc e hn] at hs)
  backward e he hs := by
    have hn : ¬selected e := fun hh ↦ he.1 ((hold e).mpr (Or.inr hh))
    rw [RibbonLabelling.retained_reverseVertexWord T.labels e M
      (fun z hz ↦ hrot z (outside_selected T selected hinv hn hz))
      (fun z hz ↦ harc z (outside_selected T selected hinv hn hz))
      (fun z hz ↦ hcorner z (outside_selected T selected hinv hn hz))]
    exact T.readings.backward e ⟨fun ho ↦ he.1 ((hold e).mpr (Or.inl ho)),
      fun hm ↦ he.2 ((replacement_sameCycle T Q selected hinv hrot T.marked hmark e).mpr hm)⟩
      (by rwa [harc e hn] at hs)

include hinv hmark hrot harc hcorner in
/-- The original marked factor shape survives literally. -/
theorem replacementShape : FactorVertexShape M T.marked := by
  have hr := replacement_sameCycle T Q selected hinv hrot T.marked hmark
  constructor
  · intro e he
    have ho := hr e |>.mp he
    rw [harc e (outside_selected T selected hinv hmark ho), harc T.marked hmark]
    exact T.shape.tag e ho
  · intro e he
    have ho := hr e |>.mp he
    have hn := outside_selected T selected hinv hmark ho
    rw [hrot e hn, harc _ (fun h ↦ hn ((hinv e).mp h)), harc e hn]
    exact T.shape.alternating e ho
  · intro e he hs
    have ho := hr e |>.mp he
    have hn := outside_selected T selected hinv hmark ho
    rw [hcorner e hn]
    exact T.shape.negative e ho (by rwa [harc e hn] at hs)

include hinv hmark hrot hcorner in
/-- Exact marked coefficient product, with no basepoint change or conjugation. -/
theorem replacementProduct : ((Q.vertexBoundary T.marked).map M.corner).prod =
    ((T.map.vertexBoundary T.marked).map T.labels.corner).prod := by
  rw [RibbonLabelling.retained_vertexBoundary T.marked
    (fun z hz ↦ hrot z (outside_selected T selected hinv hmark hz))]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact hcorner z (outside_selected T selected hinv hmark
    ((T.map.mem_vertexBoundary_iff T.marked z).mp hz))

variable (hF : RibbonLabelling.FactorCorners G M) (hE : Q.EulerEquality)
    (hfaces : ∀ e, M.faceValue e = 1)

/-- Retain the marked component of the actual replacement map. -/
noncomputable def replacement : MarkedRelativePicture G length rows {e // Q.SameComponent T.marked e} :=
  ofComponent S T.marked
    (fun ho ↦ (hold T.marked).mp ho |>.elim T.marked_not_old hmark)
    (by
      rw [RibbonLabelling.retained_vertexBoundary T.marked
        (fun z hz ↦ hrot z (outside_selected T selected hinv hmark hz))]
      exact T.marked_size)
    (replacementShape T Q M selected hinv hmark hrot harc hcorner)
    (fun h ↦ T.nontrivial ((replacementProduct T Q M selected hinv hmark hrot hcorner).symm.trans h))
    (replacementReadings T Q M S selected hinv hmark hold hrot harc hcorner)
    hF hE (fun e _ ↦ hfaces e)

/-- Every retained attaching incidence is an unselected original attaching incidence. -/
def replacementNew
    (e : {e // (replacement T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces).IsNew e}) :
    {e // T.IsNew e} := by
  refine ⟨e.val.val, fun ho ↦ e.property.1 ((hold e.val.val).mpr (Or.inl ho)), ?_⟩
  intro hm
  apply e.property.2
  apply (Q.restrict_sameVertex_iff _ _ _ _ _).mpr
  exact (replacement_sameCycle T Q selected hinv hrot T.marked hmark e.val.val).mpr hm

/-- The new-incidence inclusion reflects actual attaching vertex cycles. -/
theorem replacementNew_cycles
    (e f : {e // (replacement T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces).IsNew e}) :
    (replacement T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces).map.rotation.SameCycle
      e.val f.val ↔ T.map.rotation.SameCycle
        (replacementNew T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces e).val
        (replacementNew T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces f).val :=
  (Q.restrict_sameVertex_iff _ _ _ e.val f.val).trans
    (replacement_sameCycle T Q selected hinv hrot e.val.val
      (fun hh ↦ e.property.1 ((hold e.val.val).mpr (Or.inr hh))) f.val.val)

/-- Reclassifying any original attaching vertex as old strictly reduces the attaching count. -/
theorem replacement_count_lt (a : D) (ha : T.IsNew a) (hselected : selected a) :
    (replacement T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces).newCount < T.newCount := by
  apply T.newCount_lt_of_missing
    (replacement T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces)
    (replacementNew T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces)
    (replacementNew_cycles T Q M S selected hinv hmark hold hrot harc hcorner hF hE hfaces) a ha
  intro e he
  apply e.property.1
  apply (hold e.val.val).mpr
  exact Or.inr ((T.map.vertex_predicate_constant selected hinv he).mp hselected)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture
