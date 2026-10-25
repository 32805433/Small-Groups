module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionSystem

/-!
# Choosing the surviving component after a region split

A cut produces two affected regions on separate components. All other defective regions
come from a single original outside face. If the side away from that face contains a new
vertex it can be retained. Otherwise its old vertex equations force its sole exceptional
region to be valid, and the cut product relation restores validity on the retained side.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {D X H : Type*} [Fintype D] [Group H] {P : RibbonMap D}
    {L : RibbonLabelling P X H}

namespace OldDiscSystem

variable (S : OldDiscSystem L)

/-- If every defective face in a component is the same face, choose an actual outside
incidence there. When all equations hold, any incidence of that component is suitable. -/
theorem exists_outside_of_unique_bad (n : D)
    (hunique : ∀ d e, P.SameComponent n d → P.SameComponent n e →
      L.faceValue d ≠ 1 → L.faceValue e ≠ 1 → P.face.SameCycle d e) :
    ∃ o, P.SameComponent n o ∧
      ∀ d, P.SameComponent n d → ¬P.face.SameCycle o d → L.faceValue d = 1 := by
  classical
  by_cases h : ∃ o, P.SameComponent n o ∧ L.faceValue o ≠ 1
  · obtain ⟨o, ho, hv⟩ := h
    refine ⟨o, ho, fun d hd hn ↦ ?_⟩
    by_contra hvd
    exact hn (hunique o d ho hd hv hvd)
  · refine ⟨n, Relation.EqvGen.refl _, fun d hd _ ↦ ?_⟩
    by_contra hv
    exact h ⟨d, hd, hv⟩

/-- A single affected region and a single inherited outside region cannot create two
exceptions when an inherited defect forces the affected region equation. -/
theorem exists_outside_of_one_affected (a n : D)
    (hunique : ∀ d e, ¬P.face.SameCycle a d → ¬P.face.SameCycle a e →
      L.faceValue d ≠ 1 → L.faceValue e ≠ 1 → P.face.SameCycle d e)
    (hrestore : (∃ d, ¬P.face.SameCycle a d ∧ L.faceValue d ≠ 1) →
      L.faceValue a = 1) :
    ∃ o, P.SameComponent n o ∧
      ∀ d, P.SameComponent n d → ¬P.face.SameCycle o d → L.faceValue d = 1 := by
  classical
  apply exists_outside_of_unique_bad n
  intro d e _ _ hd he
  by_cases ho : ∃ d, ¬P.face.SameCycle a d ∧ L.faceValue d ≠ 1
  · have ha := hrestore ho
    exact hunique d e
      (fun h ↦ hd ((L.faceValue_eq_one_of_sameCycle h).mp ha))
      (fun h ↦ he ((L.faceValue_eq_one_of_sameCycle h).mp ha)) hd he
  · have hda : P.face.SameCycle a d := by
      by_contra h; exact ho ⟨d, h, hd⟩
    have hea : P.face.SameCycle a e := by
      by_contra h; exact ho ⟨e, h, he⟩
    exact hda.symm.trans hea

/-- A general two-component region-selection lemma. The inherited outside face is allowed
to be nontrivial. The algebraic exchange hypothesis is needed only if such a third,
unaffected defective face actually survives. -/
theorem extract_across_split (hE : P.EulerEquality) (a b : D)
    (hsep : ¬ P.SameComponent a b)
    (hcover : ∀ d, P.SameComponent d a ∨ P.SameComponent d b)
    (hunique : ∀ d e, ¬P.face.SameCycle a d → ¬P.face.SameCycle b d →
      ¬P.face.SameCycle a e → ¬P.face.SameCycle b e →
      L.faceValue d ≠ 1 → L.faceValue e ≠ 1 → P.face.SameCycle d e)
    (hexchange : (∃ d, ¬P.face.SameCycle a d ∧ ¬P.face.SameCycle b d ∧
      L.faceValue d ≠ 1) → (L.faceValue a = 1 ↔ L.faceValue b = 1))
    (n : D) (hn : ¬S.old n) :
    ∃ m o, ¬S.old m ∧ P.SameComponent m o ∧
      ∀ d, P.SameComponent m d → ¬P.face.SameCycle o d → L.faceValue d = 1 := by
  classical
  have face_component {d e : D} (h : P.face.SameCycle d e) : P.SameComponent d e :=
    P.component_of_faceCycle h
  have choose (m : D) (hm : ¬S.old m)
      (h : ∀ d e, P.SameComponent m d → P.SameComponent m e →
        L.faceValue d ≠ 1 → L.faceValue e ≠ 1 → P.face.SameCycle d e) :
      ∃ m o, ¬S.old m ∧ P.SameComponent m o ∧
        ∀ d, P.SameComponent m d → ¬P.face.SameCycle o d → L.faceValue d = 1 := by
    obtain ⟨o, ho, hf⟩ := exists_outside_of_unique_bad m h
    exact ⟨m, o, hm, ho, hf⟩
  have pick (x y : D) (hxy : ¬P.SameComponent x y)
      (hcov : ∀ d, P.SameComponent d x ∨ P.SameComponent d y)
      (hfar : ∀ d, P.SameComponent y d → ¬P.face.SameCycle y d → L.faceValue d = 1)
      (htrans : L.faceValue y = 1 → L.faceValue x = 1)
      (huniq : L.faceValue x = 1 → L.faceValue y = 1 →
        ∀ d e, L.faceValue d ≠ 1 → L.faceValue e ≠ 1 → P.face.SameCycle d e) :
      ∃ m o, ¬S.old m ∧ P.SameComponent m o ∧
        ∀ d, P.SameComponent m d → ¬P.face.SameCycle o d → L.faceValue d = 1 := by
    by_cases hnew : ∃ m, P.SameComponent y m ∧ ¬S.old m
    · obtain ⟨m, hm, hnew⟩ := hnew
      exact ⟨m, y, hnew, Relation.EqvGen.symm _ _ hm,
        fun d hd hf ↦ hfar d (Relation.EqvGen.trans _ _ _ hm hd) hf⟩
    · have hy := S.component_outside_eq_one y
        (fun d hd ↦ by by_contra h; exact hnew ⟨d, hd, h⟩) hE hfar
      exact choose n hn (fun d e _ _ hd he ↦ huniq (htrans hy) hy d e hd he)
  by_cases ho : ∃ d, ¬P.face.SameCycle a d ∧ ¬P.face.SameCycle b d ∧ L.faceValue d ≠ 1
  · obtain ⟨o, hoa, hob, hov⟩ := ho
    have hiff := hexchange ⟨o, hoa, hob, hov⟩
    have hunique_all (ha : L.faceValue a = 1) (hb : L.faceValue b = 1)
        (d e : D) (hd : L.faceValue d ≠ 1) (he : L.faceValue e ≠ 1) :
        P.face.SameCycle d e := by
      apply hunique d e
      · intro h; exact hd ((L.faceValue_eq_one_of_sameCycle h).mp ha)
      · intro h; exact hd ((L.faceValue_eq_one_of_sameCycle h).mp hb)
      · intro h; exact he ((L.faceValue_eq_one_of_sameCycle h).mp ha)
      · intro h; exact he ((L.faceValue_eq_one_of_sameCycle h).mp hb)
      · exact hd
      · exact he
    have far (x y : D) (hxy : ¬P.SameComponent x y) (hox : P.SameComponent o x)
        (hp : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
        ∀ d, P.SameComponent y d → ¬P.face.SameCycle y d → L.faceValue d = 1 := by
      intro d hd hface
      by_contra hv
      have hxface : ¬P.face.SameCycle x d := by
        intro h
        exact hxy (Relation.EqvGen.trans _ _ _ (face_component h)
          (Relation.EqvGen.symm _ _ hd))
      have hdo : P.face.SameCycle d o := by
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hunique d o hxface hface hoa hob hv hov
        · exact hunique d o hface hxface hoa hob hv hov
      exact hxy (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hox)
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (face_component hdo))
          (Relation.EqvGen.symm _ _ hd)))
    rcases hcover o with ha | hb
    · exact pick a b hsep hcover (far a b hsep ha (Or.inl ⟨rfl, rfl⟩))
        hiff.mpr hunique_all
    · have hsep' : ¬P.SameComponent b a := fun h ↦ hsep (Relation.EqvGen.symm _ _ h)
      exact pick b a hsep' (fun d ↦ (hcover d).symm)
        (far b a hsep' hb (Or.inr ⟨rfl, rfl⟩)) hiff.mp
        (fun hb ha ↦ hunique_all ha hb)
  · have supported (d : D) (hd : L.faceValue d ≠ 1) :
        P.face.SameCycle a d ∨ P.face.SameCycle b d := by
      by_contra h
      exact ho ⟨d, (not_or.mp h).1, (not_or.mp h).2, hd⟩
    apply choose n hn
    intro d e hnd hne hd he
    rcases supported d hd with hda | hdb <;> rcases supported e he with hea | heb
    · exact hda.symm.trans hea
    · exact False.elim (hsep (Relation.EqvGen.trans _ _ _ (face_component hda)
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hnd)
          (Relation.EqvGen.trans _ _ _ hne (Relation.EqvGen.symm _ _ (face_component heb))))))
    · exact False.elim (hsep (Relation.EqvGen.trans _ _ _ (face_component hea)
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hne)
          (Relation.EqvGen.trans _ _ _ hnd (Relation.EqvGen.symm _ _ (face_component hdb))))))
    · exact hdb.symm.trans heb

end OldDiscSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
