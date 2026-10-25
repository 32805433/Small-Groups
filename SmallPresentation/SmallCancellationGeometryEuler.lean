module

public import SmallPresentation.SmallCancellationGeometryEulerGradients
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The Euler upper bound for arbitrary finite ribbon maps

Vertex and face gradients are orthogonal in the rational edge-function space. Their kernels
are component functions. Rank-nullity therefore proves `V + F ≤ E + 2 C` for every finite
ribbon map, without a topological realization or a planarity assumption.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open Module
open scoped BigOperators

variable {D : Type*} [Fintype D] (P : RibbonMap D)

/-- Vertex and face gradients have zero dot product on the actual dart set. -/
theorem gradient_dot_zero (f : fixedSpace P.rotation) (g : fixedSpace P.face) :
    ∑ d, (P.gradient P.rotation f).val d * (P.gradient P.face g).val d = 0 := by
  have hα (d : D) : P.edge (P.edge d) = d := P.edge_involutive d
  have hs (d : D) : f.val (P.rotation.symm d) = f.val d := by
    have h := f.property (P.rotation.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hf (d : D) : g.val (P.edge d) = g.val (P.rotation.symm d) := by
    have h := g.property (P.edge d)
    change g.val (P.rotation.symm (P.edge (P.edge d))) = g.val (P.edge d) at h
    rw [hα] at h
    exact h.symm
  have h₁ : (∑ d, f.val (P.edge d) * g.val (P.edge d)) =
      ∑ d, f.val d * g.val d := Equiv.sum_comp P.edge (fun d ↦ f.val d * g.val d)
  have h₂ : (∑ d, f.val (P.edge d) * g.val d) =
      ∑ d, f.val d * g.val (P.edge d) := by
    simpa only [hα] using Equiv.sum_comp P.edge (fun d ↦ f.val d * g.val (P.edge d))
  have h₃ : (∑ d, f.val d * g.val (P.edge d)) = ∑ d, f.val d * g.val d := by
    calc
      _ = ∑ d, f.val (P.rotation.symm d) * g.val (P.rotation.symm d) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [hs, hf]
      _ = _ := Equiv.sum_comp P.rotation.symm (fun d ↦ f.val d * g.val d)
  simp only [gradient_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [h₁, h₂, h₃]
  ring

/-- Positivity over the rationals makes the two gradient ranges disjoint. -/
theorem gradient_ranges_disjoint :
    Disjoint (P.gradient P.rotation).range (P.gradient P.face).range := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨f, hf⟩ := hx
  obtain ⟨g, hg⟩ := hy
  have h := P.gradient_dot_zero f g
  rw [hf, hg] at h
  apply Subtype.ext
  funext d
  exact (Finset.sum_mul_self_eq_zero_iff Finset.univ x.val).mp h d (Finset.mem_univ d)

/-- Every finite ribbon map satisfies the Euler upper bound, component by component in total. -/
theorem euler_upper_bound :
    Fintype.card P.Vertex + Fintype.card P.Face ≤
      Fintype.card P.Edge + 2 * Fintype.card P.Component := by
  have h := Submodule.finrank_add_finrank_le_of_disjoint P.gradient_ranges_disjoint
  rw [P.finrank_edgeSpace] at h
  have hv := P.vertex_gradient_rank
  have hf := P.face_gradient_rank
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
