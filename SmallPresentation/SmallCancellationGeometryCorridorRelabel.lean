module

public import SmallPresentation.SmallCancellationGeometryCorridorCuts

/-!
# Relabelling preserves actual ribbon cells and components
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D E : Type*} (P : RibbonMap D) (Q : RibbonMap E)

/-- A bijection intertwining the actual edge and vertex permutations also intertwines faces. -/
theorem relabel_face (e : D ≃ E) (he : ∀ d, e (P.edge d) = Q.edge (e d))
    (hr : ∀ d, e (P.rotation d) = Q.rotation (e d)) (d : D) :
    e (P.face d) = Q.face (e d) := by
  apply Q.rotation.injective
  change Q.rotation (e (P.rotation.symm (P.edge d))) =
    Q.rotation (Q.rotation.symm (Q.edge (e d)))
  rw [← hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply, he]

theorem relabel_component_iff (e : D ≃ E) (he : ∀ d, e (P.edge d) = Q.edge (e d))
    (hr : ∀ d, e (P.rotation d) = Q.rotation (e d)) (d f : D) :
    P.SameComponent d f ↔ Q.SameComponent (e d) (e f) := by
  constructor
  · exact P.map_components Q e (fun d ↦ by rw [he]; exact Q.component_edge _)
      (fun d ↦ by rw [hr]; exact Q.component_rotation _)
  · intro h
    have hs := Q.map_components P e.symm ?_ ?_ h
    · simpa only [Equiv.symm_apply_apply] using hs
    · intro x
      obtain ⟨d, rfl⟩ := e.surjective x
      rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact P.component_edge d
    · intro x
      obtain ⟨d, rfl⟩ := e.surjective x
      rw [← hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact P.component_rotation d

noncomputable def relabelComponentsEquiv (e : D ≃ E)
    (he : ∀ d, e (P.edge d) = Q.edge (e d))
    (hr : ∀ d, e (P.rotation d) = Q.rotation (e d)) : P.Component ≃ Q.Component :=
  Quotient.congr e (P.relabel_component_iff Q e he hr)

theorem relabel_euler_iff [Finite D] [Finite E] (e : D ≃ E)
    (he : ∀ d, e (P.edge d) = Q.edge (e d))
    (hr : ∀ d, e (P.rotation d) = Q.rotation (e d)) :
    (Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) ↔
    (Fintype.card Q.Vertex + Fintype.card Q.Face =
      Fintype.card Q.Edge + 2 * Fintype.card Q.Component) := by
  have hv := Fintype.card_congr (conjugateEquiv P.rotation Q.rotation e hr)
  have hf := Fintype.card_congr (conjugateEquiv P.face Q.face e
    (P.relabel_face Q e he hr))
  have hed := Fintype.card_congr (conjugateEquiv P.edge Q.edge e he)
  have hc := Fintype.card_congr (P.relabelComponentsEquiv Q e he hr)
  change Fintype.card P.Vertex = Fintype.card Q.Vertex at hv
  change Fintype.card P.Face = Fintype.card Q.Face at hf
  change Fintype.card P.Edge = Fintype.card Q.Edge at hed
  rw [hv, hf, hed, hc]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
