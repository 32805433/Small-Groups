module

public import SmallPresentation.SmallCancellationGeometryFaceCap

/-! Connectedness and spherical Euler equality of actual face capping. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap

variable {D : Type*} (P : RibbonMap D) (a : D)

noncomputable def oldDart (d : D) : (degreeTwo P a).Dart :=
  (degreeTwo P a).dartEquiv.symm ⟨.inl d, by simp [degreeTwo]⟩

@[simp] theorem oldDart_val (d : D) : (oldDart P a d).val = .inl d := rfl

noncomputable def oldEquiv : D ≃ (degreeTwo P a).Dart :=
  Equiv.ofBijective (oldDart P a) (by
    constructor
    · intro d e h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · intro d
      have hp := ((degreeTwo P a).dartEquiv d).property
      change d.val ≠ Sum.inr false ∧ d.val ≠ Sum.inr true at hp
      rcases hv : d.val with e | b
      · exact ⟨e, Subtype.ext hv.symm⟩
      · cases b
        · exact (hp.1 hv).elim
        · exact (hp.2 hv).elim)

theorem suppress_rotation (d : D) :
    (degreeTwo P a).suppress.rotation (oldEquiv P a d) = oldEquiv P a (P.rotation d) := by
  apply Subtype.ext
  rw [(degreeTwo P a).rotation_val]
  rfl

theorem suppress_edge (d : D) :
    (degreeTwo P a).suppress.edge (oldEquiv P a d) = oldEquiv P a (P.edge d) := by
  classical
  let B := (degreeTwo P a).dualBigon
  apply Subtype.ext
  change (B.edge (oldDart P a d)).val = Sum.inl (P.edge d)
  by_cases hl : d = P.edge a
  · subst d
    have hd : oldDart P a (P.edge a) = B.leftDart := by
      apply Subtype.ext
      exact (edge_positive P a).symm
    rw [hd, B.edge_leftDart]
    change (map P a).edge (.inr true) = .inl (P.edge (P.edge a))
    rw [edge_negative, P.edge_involutive a]
  · by_cases hr : d = a
    · subst d
      have hd : oldDart P a a = B.rightDart := by
        apply Subtype.ext
        exact (edge_negative P a).symm
      rw [hd, B.edge_rightDart]
      exact edge_positive P a
    · rw [B.edge_val_of_ne]
      · exact edge_old P a d hr hl
      · change Sum.inl d ≠ (map P a).edge (.inr false)
        rw [edge_positive]
        exact fun h ↦ hl (Sum.inl.inj h)
      · change Sum.inl d ≠ (map P a).edge (.inr true)
        rw [edge_negative]
        exact fun h ↦ hr (Sum.inl.inj h)

theorem euler [Finite D] (h : P.EulerEquality) : (map P a).EulerEquality := by
  apply (degreeTwo P a).euler_iff.mp
  apply (P.relabel_euler_iff (degreeTwo P a).suppress (oldEquiv P a)
    (fun d ↦ (suppress_edge P a d).symm)
    (fun d ↦ (suppress_rotation P a d).symm)).mp
  exact h

theorem connected (h : P.Connected) : (map P a).Connected := by
  have ha : (map P a).SameComponent (.inl a) (.inl (P.edge a)) := by
    have h1 := (map P a).component_edge (.inl a)
    have h2 := (map P a).component_rotation (.inr true)
    have h3 := (map P a).component_edge (.inr false)
    rw [edge_anchor] at h1
    rw [rotation_negative] at h2
    rw [edge_positive] at h3
    exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2 h3)
  have he (d : D) : (map P a).SameComponent (.inl d) (.inl (P.edge d)) := by
    by_cases hd : d = a
    · subst d
      exact ha
    · by_cases hm : d = P.edge a
      · subst d
        rw [P.edge_involutive a]
        exact ha.symm
      · have hh := (map P a).component_edge (.inl d)
        rwa [edge_old P a d hd hm] at hh
  have hc (d e : D) : (map P a).SameComponent (.inl d) (.inl e) :=
    P.map_components (map P a) Sum.inl he (fun d ↦ (map P a).component_rotation (.inl d)) (h d e)
  have toAnchor (d : D ⊕ Bool) : (map P a).SameComponent d (.inl a) := by
    rcases d with d | b
    · exact hc d a
    · cases b
      · have hh := (map P a).component_edge (.inr false)
        rw [edge_positive] at hh
        exact Relation.EqvGen.trans _ _ _ hh (hc _ _)
      · have hh := (map P a).component_edge (.inr true)
        rwa [edge_negative] at hh
  intro d e
  exact Relation.EqvGen.trans _ _ _ (toAnchor d) (toAnchor e).symm

theorem card_darts [Fintype D] : Fintype.card (D ⊕ Bool) = Fintype.card D + 2 := by simp

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap
