module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.FinCases

/-!
# Finite incidence counting for spherical small-cancellation diagrams

This module proves the finite counting obstruction used after bigon suppression. It does not
construct planar pictures or prove that a picture has the required incidence data. The hypotheses
are the explicit dart-to-edge, dart-to-vertex and dart-to-face maps, with two darts per edge and
the sphere Euler equation. Repeated vertices, loops and bridges require no separate arithmetic
cases: all degrees count darts, not distinct neighbors.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

open scoped BigOperators

/-- The number of dart incidences at a specified object, counted with multiplicity. -/
noncomputable def incidenceDegree {D V : Type*} [Fintype D] (incidence : D → V)
    (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun d ↦ incidence d = v)).card

/-- Every dart contributes to exactly one incidence fiber. -/
theorem sum_incidenceDegree {D V : Type*} [Fintype D] [Fintype V]
    (incidence : D → V) : ∑ v, incidenceDegree incidence v = Fintype.card D := by
  classical
  simpa [incidenceDegree] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset D)
      (Finset.univ : Finset V) incidence

/-- A uniform lower incidence bound gives the corresponding bound on the total dart count. -/
theorem incidence_lower_bound {D V : Type*} [Fintype D] [Fintype V]
    (incidence : D → V) (k : ℕ) (h : ∀ v, k ≤ incidenceDegree incidence v) :
    k * Fintype.card V ≤ Fintype.card D := by
  classical
  calc
    k * Fintype.card V = ∑ _v : V, k := by simp [Nat.mul_comm]
    _ ≤ ∑ v, incidenceDegree incidence v := Finset.sum_le_sum (fun v _ ↦ h v)
    _ = Fintype.card D := sum_incidenceDegree incidence

/-- If one specified outer face is exempt, its missing lower bound costs exactly `k`. -/
theorem incidence_lower_bound_except_one {D V : Type*} [Fintype D] [Fintype V]
    (incidence : D → V) (outside : V) (k : ℕ)
    (h : ∀ v, v ≠ outside → k ≤ incidenceDegree incidence v) :
    k * Fintype.card V ≤ Fintype.card D + k := by
  classical
  have hs : (∑ _v : V, k) ≤
      ∑ v : V, (incidenceDegree incidence v + if v = outside then k else 0) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v = outside
    · simp [hv]
    · simpa [hv] using h v hv
  simpa [Finset.sum_add_distrib, sum_incidenceDegree, Nat.mul_comm] using hs

/-- A lower bound at the exceptional incidence fiber improves the deficit estimate. -/
theorem incidence_lower_bound_with_exception {D V : Type*} [Fintype D] [Fintype V]
    (incidence : D → V) (outside : V) (k m : ℕ)
    (h : ∀ v, v ≠ outside → k ≤ incidenceDegree incidence v)
    (hout : m ≤ incidenceDegree incidence outside) :
    k * Fintype.card V + m ≤ Fintype.card D + k := by
  classical
  have hs : (∑ v : V, (k + if v = outside then m else 0)) ≤
      ∑ v : V, (incidenceDegree incidence v + if v = outside then k else 0) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v = outside
    · simp only [hv, ite_true]
      omega
    · simpa [hv] using h v hv
  simpa [Finset.sum_add_distrib, sum_incidenceDegree, Nat.mul_comm] using hs

/-- Two darts per edge identifies the total number of darts. -/
theorem card_darts_eq_twice_edges {D E : Type*} [Fintype D] [Fintype E]
    (edge : D → E) (h : ∀ e, incidenceDegree edge e = 2) :
    Fintype.card D = 2 * Fintype.card E := by
  classical
  calc
    Fintype.card D = ∑ e, incidenceDegree edge e := (sum_incidenceDegree edge).symm
    _ = ∑ _e : E, 2 := Finset.sum_congr rfl (fun e _ ↦ h e)
    _ = 2 * Fintype.card E := by simp [Nat.mul_comm]

/-- A sphere cannot have six incidences per vertex and three per inner face.
The outer face carries no degree or coefficient hypothesis. -/
theorem sphere_c6_impossible {D V E F : Type*}
    [Fintype D] [Fintype V] [Fintype E] [Fintype F]
    (vertex : D → V) (edge : D → E) (face : D → F) (outside : F)
    (hedge : ∀ e, incidenceDegree edge e = 2)
    (hvertex : ∀ v, 6 ≤ incidenceDegree vertex v)
    (hface : ∀ f, f ≠ outside → 3 ≤ incidenceDegree face f)
    (heuler : Fintype.card V + Fintype.card F = Fintype.card E + 2) : False := by
  have hv := incidence_lower_bound vertex 6 hvertex
  have hf := incidence_lower_bound_except_one face outside 3 hface
  have he := card_darts_eq_twice_edges edge hedge
  omega

/-- The same spherical obstruction allows one exceptional vertex, provided it has an
incidence. This is the counting form for a marked coefficient boundary. -/
theorem sphere_c6_boundary_impossible {D V E F : Type*}
    [Fintype D] [Fintype V] [Fintype E] [Fintype F]
    (vertex : D → V) (edge : D → E) (face : D → F) (boundary : V) (outside : F)
    (hedge : ∀ e, incidenceDegree edge e = 2)
    (hvertex : ∀ v, v ≠ boundary → 6 ≤ incidenceDegree vertex v)
    (hboundary : 1 ≤ incidenceDegree vertex boundary)
    (hface : ∀ f, f ≠ outside → 3 ≤ incidenceDegree face f)
    (heuler : Fintype.card V + Fintype.card F = Fintype.card E + 2) : False := by
  have hv := incidence_lower_bound_with_exception vertex boundary 6 1 hvertex hboundary
  have hf := incidence_lower_bound_except_one face outside 3 hface
  have he := card_darts_eq_twice_edges edge hedge
  omega

/-- The parallel incidence estimate for the reusable `C(4), T(4)` curvature case. -/
theorem sphere_c4_t4_impossible {D V E F : Type*}
    [Fintype D] [Fintype V] [Fintype E] [Fintype F]
    (vertex : D → V) (edge : D → E) (face : D → F) (outside : F)
    (hedge : ∀ e, incidenceDegree edge e = 2)
    (hvertex : ∀ v, 4 ≤ incidenceDegree vertex v)
    (hface : ∀ f, f ≠ outside → 4 ≤ incidenceDegree face f)
    (heuler : Fintype.card V + Fintype.card F = Fintype.card E + 2) : False := by
  have hv := incidence_lower_bound vertex 4 hvertex
  have hf := incidence_lower_bound_except_one face outside 4 hface
  have he := card_darts_eq_twice_edges edge hedge
  omega

/-- The parallel incidence estimate for the reusable `C(3), T(6)` curvature case. -/
theorem sphere_c3_t6_impossible {D V E F : Type*}
    [Fintype D] [Fintype V] [Fintype E] [Fintype F]
    (vertex : D → V) (edge : D → E) (face : D → F) (outside : F)
    (hedge : ∀ e, incidenceDegree edge e = 2)
    (hvertex : ∀ v, 3 ≤ incidenceDegree vertex v)
    (hface : ∀ f, f ≠ outside → 6 ≤ incidenceDegree face f)
    (heuler : Fintype.card V + Fintype.card F = Fintype.card E + 2) : False := by
  have hv := incidence_lower_bound vertex 3 hvertex
  have hf := incidence_lower_bound_except_one face outside 6 hface
  have he := card_darts_eq_twice_edges edge hedge
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
