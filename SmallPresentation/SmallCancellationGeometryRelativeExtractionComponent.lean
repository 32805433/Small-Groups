module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionMetric

/-! Matching original incidences in each genuine new-containing component. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.OldDiscSystem

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D Q : Type*} [Fintype D] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)}
    {q : Monoid.CoprodI G →* Q}

/-- Each new-containing component of a spherical mixed picture supplies two matching
original incidences. Membership is in the original component, before any normalization. -/
theorem exists_matched_in_component (S : OldDiscSystem L) (R : MixedReadings (rows := rows) S)
    (F : CornerPotential L q) (hE : P.EulerEquality)
    (hregions : ∀ d, L.faceValue d = 1)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) (n : D) (hn : ¬S.old n) :
    ∃ (d e : D) (hd : ¬S.old d) (he : ¬S.old e),
      P.SameComponent n d ∧ P.SameComponent n e ∧ d ≠ e ∧
      (L.arc d).2 = true ∧ L.arc e = reverseLetter (L.arc d) ∧
      R.origin ⟨e, he⟩ = R.origin ⟨d, hd⟩ ∧ F.value e = F.value d := by
  classical
  let p := P.SameComponent n
  let he := P.component_membership_edge n
  let hr := P.component_membership_rotation n
  let E := {d // p d}
  let a : E := ⟨n, Relation.EqvGen.refl _⟩
  let M := L.restrict p he hr
  let T := S.restrict p he hr
  let K := F.restrict p he hr
  have hc : (P.restrict p he hr).Connected := P.componentRibbon_connected n
  have hEuler : (P.restrict p he hr).EulerEquality := P.restrict_euler p he hr hE
  obtain ⟨W⟩ := exists_extraction E (P.restrict p he hr) M T K a hc hEuler
    (fun d _ ↦ (L.restrict_faceValue p he hr d).trans (hregions d.val)) a hn
  obtain ⟨d, e, hd, he', hne, hpos, harc, horigin, hvalue⟩ :=
    W.exists_matched_original (R.restrict p he hr) hidentity hreduced hmetric
  exact ⟨d.val, e.val, hd, he', d.property, e.property,
    fun h ↦ hne (Subtype.ext h), hpos, harc, horigin, hvalue⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.OldDiscSystem
