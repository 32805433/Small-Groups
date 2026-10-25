module

public import SmallPresentation.SmallCancellationGeometryEulerRestriction
public import SmallPresentation.SmallCancellationGeometryCorridorSuppression

/-! Each actual nonempty component of a spherical ribbon is itself spherical. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} (P : RibbonMap D)

theorem component_membership_edge (a d : D) :
    P.SameComponent a (P.edge d) ↔ P.SameComponent a d := by
  constructor
  · intro h
    exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ (P.component_edge d))
  · intro h
    exact Relation.EqvGen.trans _ _ _ h (P.component_edge d)

theorem component_membership_rotation (a d : D) :
    P.SameComponent a (P.rotation d) ↔ P.SameComponent a d := by
  constructor
  · intro h
    exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ (P.component_rotation d))
  · intro h
    exact Relation.EqvGen.trans _ _ _ h (P.component_rotation d)

/-- Restriction to the actual connected component containing a given dart. -/
noncomputable def componentRibbon (a : D) : RibbonMap {d : D // P.SameComponent a d} :=
  P.restrict (P.SameComponent a) (P.component_membership_edge a)
    (P.component_membership_rotation a)

theorem componentRibbon_connected (a : D) : (P.componentRibbon a).Connected := by
  intro d e
  apply (P.restrict_sameComponent_iff _ _ _ d e).mpr
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ d.property) e.property

/-- A nonempty connected ribbon has exactly one component. -/
theorem card_components_of_connected [Finite D] (hc : P.Connected) (a : D) :
    Fintype.card P.Component = 1 := by
  let : Unique P.Component := {
    default := Quotient.mk _ a
    uniq := fun c ↦ by
      induction c using Quotient.inductionOn with
      | h d => exact Quotient.sound (hc d a) }
  exact Fintype.card_unique

theorem componentRibbon_card_components [Finite D] (a : D) :
    Fintype.card (P.componentRibbon a).Component = 1 :=
  (P.componentRibbon a).card_components_of_connected (P.componentRibbon_connected a)
    ⟨a, Relation.EqvGen.refl a⟩

/-- Global spherical Euler characteristic supplies the sphere equation on each actual component. -/
theorem componentRibbon_sphere [Fintype D]
    (h : Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) (a : D) :
    Fintype.card (P.componentRibbon a).Vertex + Fintype.card (P.componentRibbon a).Face =
      Fintype.card (P.componentRibbon a).Edge + 2 := by
  have hh := P.restrict_euler (P.SameComponent a) (P.component_membership_edge a)
    (P.component_membership_rotation a) h
  change Fintype.card (P.componentRibbon a).Vertex + Fintype.card (P.componentRibbon a).Face =
    Fintype.card (P.componentRibbon a).Edge + 2 * Fintype.card (P.componentRibbon a).Component at hh
  simpa only [P.componentRibbon_card_components a, mul_one] using hh

/-- If both edge and rotation exchange a pair, that pair is an entire component. -/
theorem isolated_two_dart_component (a b : D) (ha : P.edge a = b)
    (hr₁ : P.rotation a = b) (hr₂ : P.rotation b = a) {d : D}
    (h : P.SameComponent a d) : d = a ∨ d = b := by
  have hb : P.edge b = a := by rw [← ha, P.edge_involutive a]
  exact (P.invariant_on_component (fun d ↦ d = a ∨ d = b)
    (PermutationCycles.twoCycle_invariant P.edge a b ha hb)
    (PermutationCycles.twoCycle_invariant P.rotation a b hr₁ hr₂) h).mp (Or.inl rfl)

/-- A connected component containing another dart cannot be the isolated corridor loop. -/
theorem degreeTwo_edge_ne (hc : P.Connected) (a b z : D)
    (hr₁ : P.rotation a = b) (hr₂ : P.rotation b = a) (hza : z ≠ a) (hzb : z ≠ b) :
    P.edge a ≠ b := by
  intro ha
  rcases P.isolated_two_dart_component a b ha hr₁ hr₂ (hc a z) with h | h
  · exact hza h
  · exact hzb h

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
