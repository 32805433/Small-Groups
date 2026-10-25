module

public import SmallPresentation.SmallCancellationGeometryEuler
public import SmallPresentation.PermutationCyclePartition

/-!
# Restriction to invariant unions of ribbon components

The edge, vertex, face and component counts are additive across an invariant dart partition.
Together with the general Euler upper bound, this proves that a globally spherical ribbon
has spherical Euler characteristic on every union of its actual components.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

attribute [local instance] Classical.propDecidable

variable {D : Type*} (P : RibbonMap D) (p : D → Prop)
    (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d)

/-- Restrict both incidence permutations to an invariant dart subset. -/
noncomputable def restrict : RibbonMap {d : D // p d} where
  edge := P.edge.subtypePerm he
  edge_involutive d := Subtype.ext (P.edge_involutive d.val)
  edge_ne d h := P.edge_ne d.val (congrArg Subtype.val h)
  rotation := P.rotation.subtypePerm hr

@[simp] theorem restrict_edge_val (d : {d : D // p d}) :
    ((P.restrict p he hr).edge d).val = P.edge d.val := rfl

@[simp] theorem restrict_rotation_val (d : {d : D // p d}) :
    ((P.restrict p he hr).rotation d).val = P.rotation d.val := rfl

include he hr in
theorem restrict_face_invariant (d : D) : p (P.face d) ↔ p d := by
  have h := hr (P.rotation.symm (P.edge d))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm.trans (he d)

theorem restrict_face :
    (P.restrict p he hr).face = P.face.subtypePerm (P.restrict_face_invariant p he hr) := by
  apply Equiv.ext
  intro d
  rfl

theorem restrict_sameComponent_iff (d e : {d : D // p d}) :
    (P.restrict p he hr).SameComponent d e ↔ P.SameComponent d.val e.val := by
  constructor
  · intro h
    exact (P.restrict p he hr).map_components P Subtype.val
      (fun d ↦ P.component_edge d.val) (fun d ↦ P.component_rotation d.val) h
  · have liftPath {x y : D} (h : P.SameComponent x y) : ∀ hx hy,
        (P.restrict p he hr).SameComponent ⟨x, hx⟩ ⟨y, hy⟩ := by
      induction h with
      | rel x y h =>
        intro hx hy
        apply Relation.EqvGen.rel
        rcases h with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      | refl x => intro hx hy; exact Relation.EqvGen.refl _
      | symm x y _ ih => intro hx hy; exact Relation.EqvGen.symm _ _ (ih hy hx)
      | trans x y z hxy _ ih₁ ih₂ =>
        intro hx hz
        have hy := (P.invariant_on_component p he hr hxy).mp hx
        exact Relation.EqvGen.trans _ _ _ (ih₁ hx hy) (ih₂ hy hz)
    intro h
    exact liftPath h d.property e.property

/-- An invariant predicate descends to the actual component quotient. -/
noncomputable def componentPredicate : P.Component → Prop :=
  Quotient.lift p (fun _ _ h ↦ propext (P.invariant_on_component p he hr h))

noncomputable def restrictComponentsEquiv :
    {c : P.Component // P.componentPredicate p he hr c} ≃ (P.restrict p he hr).Component :=
  Equiv.subtypeQuotientEquivQuotientSubtype p (P.componentPredicate p he hr)
    (fun _ ↦ Iff.rfl) (P.restrict_sameComponent_iff p he hr)

/-- Exact decomposition of components across an invariant dart partition. -/
noncomputable def partitionComponentsEquiv : P.Component ≃
    (P.restrict p he hr).Component ⊕
      (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
        (fun d ↦ not_congr (hr d))).Component := by
  let en : {c : P.Component // ¬P.componentPredicate p he hr c} ≃
      (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
        (fun d ↦ not_congr (hr d))).Component :=
    Equiv.subtypeQuotientEquivQuotientSubtype (fun d ↦ ¬p d)
    (fun c ↦ ¬P.componentPredicate p he hr c) (fun _ ↦ Iff.rfl)
    (P.restrict_sameComponent_iff (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
      (fun d ↦ not_congr (hr d)))
  exact (Equiv.sumCompl (P.componentPredicate p he hr)).symm.trans
    (Equiv.sumCongr (P.restrictComponentsEquiv p he hr) en)

theorem partition_card_vertices [Finite D] : Fintype.card P.Vertex =
    Fintype.card (P.restrict p he hr).Vertex +
    Fintype.card (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
      (fun d ↦ not_congr (hr d))).Vertex := by
  let := Fintype.ofFinite (PermutationCycles.Cycles (P.rotation.subtypePerm hr))
  let := Fintype.ofFinite (PermutationCycles.Cycles
    (PermutationCycles.complementPerm P.rotation p hr))
  exact PermutationCycles.card_partitionCycles P.rotation p hr

theorem partition_card_edges [Finite D] : Fintype.card P.Edge =
    Fintype.card (P.restrict p he hr).Edge +
    Fintype.card (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
      (fun d ↦ not_congr (hr d))).Edge := by
  let := Fintype.ofFinite (PermutationCycles.Cycles (P.edge.subtypePerm he))
  let := Fintype.ofFinite (PermutationCycles.Cycles
    (PermutationCycles.complementPerm P.edge p he))
  exact PermutationCycles.card_partitionCycles P.edge p he

theorem partition_card_faces [Finite D] : Fintype.card P.Face =
    Fintype.card (P.restrict p he hr).Face +
    Fintype.card (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
      (fun d ↦ not_congr (hr d))).Face := by
  let hp := P.restrict_face_invariant p he hr
  let := Fintype.ofFinite (PermutationCycles.Cycles (P.face.subtypePerm hp))
  let := Fintype.ofFinite (PermutationCycles.Cycles
    (PermutationCycles.complementPerm P.face p hp))
  have hc := PermutationCycles.card_partitionCycles P.face p hp
  simp only [Fintype.card_eq_nat_card] at hc ⊢
  change Nat.card (PermutationCycles.Cycles P.face) =
    Nat.card (PermutationCycles.Cycles (P.restrict p he hr).face) +
      Nat.card (PermutationCycles.Cycles (P.restrict (fun d ↦ ¬p d)
        (fun d ↦ not_congr (he d)) (fun d ↦ not_congr (hr d))).face)
  rw [P.restrict_face p he hr,
    P.restrict_face (fun d ↦ ¬p d) (fun d ↦ not_congr (he d)) (fun d ↦ not_congr (hr d))]
  exact hc

theorem partition_card_components [Finite D] : Fintype.card P.Component =
    Fintype.card (P.restrict p he hr).Component +
    Fintype.card (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
      (fun d ↦ not_congr (hr d))).Component := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (P.partitionComponentsEquiv p he hr)

/-- Equality in the Euler upper bound passes to every invariant restriction. -/
theorem restrict_euler [Fintype D]
    (h : Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) :
    Fintype.card (P.restrict p he hr).Vertex + Fintype.card (P.restrict p he hr).Face =
      Fintype.card (P.restrict p he hr).Edge + 2 * Fintype.card (P.restrict p he hr).Component := by
  have hv := P.partition_card_vertices p he hr
  have hf := P.partition_card_faces p he hr
  have he' := P.partition_card_edges p he hr
  have hc := P.partition_card_components p he hr
  have h₁ := (P.restrict p he hr).euler_upper_bound
  have h₂ := (P.restrict (fun d ↦ ¬p d) (fun d ↦ not_congr (he d))
    (fun d ↦ not_congr (hr d))).euler_upper_bound
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
