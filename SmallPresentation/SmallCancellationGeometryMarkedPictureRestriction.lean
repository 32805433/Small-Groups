module

public import SmallPresentation.SmallCancellationGeometryMarkedPictureCounts

/-! Restrict marked mixed data to the actual component of the distinguished boundary. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)}

attribute [local instance] Classical.propDecidable

/-- Exact original row readings pass to any invariant union containing the marked vertex. -/
noncomputable def MarkedMixedReadings.restrict {S : OldDiscSystem L} {m : D}
    (R : MarkedMixedReadings G length rows S m) (p : D → Prop)
    (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d) (hm : p m) :
    MarkedMixedReadings G length rows (S.restrict p he hr) ⟨m, hm⟩ where
  origin d := R.origin ⟨d.val.val, d.property.1,
    fun h ↦ d.property.2 ((P.restrict_sameVertex_iff p he hr _ _).mpr h)⟩
  forward d hd ha := by
    rw [L.restrict_vertexWord p he hr]
    exact R.forward d.val ⟨hd.1,
      fun h ↦ hd.2 ((P.restrict_sameVertex_iff p he hr _ _).mpr h)⟩ ha
  backward d hd ha := by
    rw [L.restrict_reverseVertexWord p he hr]
    exact R.backward d.val ⟨hd.1,
      fun h ↦ hd.2 ((P.restrict_sameVertex_iff p he hr _ _).mpr h)⟩ ha

omit [Fintype D] in
/-- Local phase and coefficient support are inherited literally by component restriction. -/
theorem RibbonLabelling.FactorCorners.restrict (F : RibbonLabelling.FactorCorners G L)
    (p : D → Prop) (he : ∀ d, p (P.edge d) ↔ p d)
    (hr : ∀ d, p (P.rotation d) ↔ p d) :
    RibbonLabelling.FactorCorners G (L.restrict p he hr) where
  alternating d := F.alternating d.val
  positive_tag d := F.positive_tag d.val
  negative_one d := F.negative_one d.val
  coefficient d := F.coefficient d.val

namespace MarkedRelativePicture

variable (S : OldDiscSystem L) (m : D) (hm : ¬S.old m)
    (hsize : (P.vertexBoundary m).length = 2)
    (shape : FactorVertexShape L m)
    (nontrivial : ((P.vertexBoundary m).map L.corner).prod ≠ 1)
    (readings : MarkedMixedReadings G length rows S m)
    (factors : RibbonLabelling.FactorCorners G L) (hEuler : P.EulerEquality)
    (hfaces : ∀ d, P.SameComponent m d → L.faceValue d = 1)

/-- A possibly disconnected result of surgery gives a genuine marked picture by retaining
its marked component. Every equation is inherited from that actual component. -/
noncomputable def ofComponent :
    MarkedRelativePicture G length rows {d // P.SameComponent m d} where
  map := P.componentRibbon m
  labels := L.restrict (P.SameComponent m) (P.component_membership_edge m)
    (P.component_membership_rotation m)
  marked := ⟨m, Relation.EqvGen.refl _⟩
  marked_size := by
    have hh := congrArg List.length (P.restrict_vertexBoundary (P.SameComponent m)
      (P.component_membership_edge m) (P.component_membership_rotation m)
      ⟨m, Relation.EqvGen.refl _⟩)
    simpa only [RibbonMap.componentRibbon, List.length_map, hsize] using hh
  oldDiscs := S.restrict (P.SameComponent m) (P.component_membership_edge m)
    (P.component_membership_rotation m)
  marked_not_old := hm
  shape := {
    tag := fun d hd ↦ shape.tag d.val ((P.restrict_sameVertex_iff _ _ _ _ _).mp hd)
    alternating := fun d hd ↦ shape.alternating d.val ((P.restrict_sameVertex_iff _ _ _ _ _).mp hd)
    negative := fun d hd ↦ shape.negative d.val ((P.restrict_sameVertex_iff _ _ _ _ _).mp hd) }
  nontrivial := by
    intro h
    apply nontrivial
    have hh := P.restrict_vertexBoundary (P.SameComponent m) (P.component_membership_edge m)
      (P.component_membership_rotation m) ⟨m, Relation.EqvGen.refl _⟩
    rw [← hh, List.map_map]
    exact h
  readings := readings.restrict (P.SameComponent m) (P.component_membership_edge m)
    (P.component_membership_rotation m) (Relation.EqvGen.refl _)
  factorCorners := factors.restrict _ _ _
  connected := P.componentRibbon_connected m
  euler := P.restrict_euler _ _ _ hEuler
  faces := fun d ↦ (L.restrict_faceValue _ _ _ d).trans (hfaces d.val d.property)

/-- New incidences after component selection are precisely the surviving original
incidences which were neither old nor marked. -/
theorem ofComponent_isNew (d : {d // P.SameComponent m d}) :
    (ofComponent S m hm hsize shape nontrivial readings factors hEuler hfaces).IsNew d ↔
      ¬S.old d.val ∧ ¬P.rotation.SameCycle m d.val := by
  change (¬S.old d.val ∧ ¬(P.componentRibbon m).rotation.SameCycle
    ⟨m, Relation.EqvGen.refl _⟩ d) ↔ _
  exact and_congr Iff.rfl (not_congr (P.restrict_sameVertex_iff
    (P.SameComponent m) (P.component_membership_edge m)
    (P.component_membership_rotation m) ⟨m, Relation.EqvGen.refl _⟩ d))

end MarkedRelativePicture
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
