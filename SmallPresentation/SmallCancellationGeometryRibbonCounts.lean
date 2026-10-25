module

public import SmallPresentation.SmallCancellationGeometryRibbon

/-!
# Counting the actual cycles of a ribbon map

The edge involution determines the actual edge quotient. Every edge fiber has exactly two darts,
so the abstract incidence count from `SmallCancellationGeometryCounts` applies to these ribbon
maps. The bridge operation preserves the number of edges and vertices. Its face count is not
claimed to be preserved: the missing planar bridge lemma must control that separately.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} (P : RibbonMap D)

private theorem boundary_nodup (p : Equiv.Perm D) (d : D) :
    (List.ofFn (fun k : Fin (Function.minimalPeriod p d) ↦ (p ^ k.val) d)).Nodup := by
  apply List.nodup_ofFn.mpr
  intro k l h
  apply Fin.ext
  apply Function.iterate_injOn_Iio_minimalPeriod k.isLt l.isLt
  simpa only [Equiv.Perm.coe_pow] using h

private theorem mem_boundary_iff [Finite D] (p : Equiv.Perm D) (d e : D) :
    e ∈ List.ofFn (fun k : Fin (Function.minimalPeriod p d) ↦ (p ^ k.val) d) ↔
      p.SameCycle d e := by
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨k, rfl⟩
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts d)
    refine ⟨⟨n % Function.minimalPeriod p d, Nat.mod_lt _ hp⟩, ?_⟩
    change (p ^ (n % Function.minimalPeriod p d)) d = e
    calc
      (p ^ (n % Function.minimalPeriod p d)) d = (p ^ n) d := by
        simpa only [Equiv.Perm.coe_pow] using
          (Function.iterate_mod_minimalPeriod_eq (f := (p : D → D)) (x := d) (n := n))
      _ = e := hn

/-- The based vertex traversal visits each incident dart exactly once. -/
theorem vertexBoundary_nodup (d : D) : (P.vertexBoundary d).Nodup :=
  boundary_nodup P.rotation d

/-- The based face traversal visits each incident dart exactly once. -/
theorem faceBoundary_nodup (d : D) : (P.faceBoundary d).Nodup :=
  boundary_nodup P.face d

/-- A vertex traversal is precisely its actual rotation cycle. -/
theorem mem_vertexBoundary_iff [Finite D] (d e : D) :
    e ∈ P.vertexBoundary d ↔ P.rotation.SameCycle d e :=
  mem_boundary_iff P.rotation d e

/-- A face traversal is precisely its actual face cycle. -/
theorem mem_faceBoundary_iff [Finite D] (d e : D) :
    e ∈ P.faceBoundary d ↔ P.face.SameCycle d e :=
  mem_boundary_iff P.face d e

/-- Edges are the cycles of the dart-pairing involution. -/
abbrev Edge := Quotient (Equiv.Perm.SameCycle.setoid P.edge)

/-- The edge containing a dart. -/
def edgeOf (d : D) : P.Edge := Quotient.mk _ d

noncomputable instance vertexFintype [Finite D] : Fintype P.Vertex := Fintype.ofFinite _
noncomputable instance edgeFintype [Finite D] : Fintype P.Edge := Fintype.ofFinite _
noncomputable instance faceFintype [Finite D] : Fintype P.Face := Fintype.ofFinite _

set_option backward.isDefEq.respectTransparency false in
/-- The degree of an actual vertex equals the length of its explicit cyclic boundary. -/
theorem vertex_incidenceDegree [Fintype D] (d : D) :
    incidenceDegree P.vertexOf (P.vertexOf d) = (P.vertexBoundary d).length := by
  classical
  have hset : Finset.univ.filter (fun e ↦ P.vertexOf e = P.vertexOf d) =
      (P.vertexBoundary d).toFinset := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
      P.mem_vertexBoundary_iff]
    constructor
    · intro h
      exact (Quotient.exact h).symm
    · intro h
      exact Quotient.sound h.symm
  have hcard : (Finset.univ.filter (fun e ↦ P.vertexOf e = P.vertexOf d)).card =
      (P.vertexBoundary d).length := by
    rw [hset, List.toFinset_card_of_nodup (P.vertexBoundary_nodup d)]
  simpa only [incidenceDegree, vertexOf, faceOf] using hcard

set_option backward.isDefEq.respectTransparency false in
/-- The degree of an actual face equals the length of its explicit cyclic boundary. -/
theorem face_incidenceDegree [Fintype D] (d : D) :
    incidenceDegree P.faceOf (P.faceOf d) = (P.faceBoundary d).length := by
  classical
  have hset : Finset.univ.filter (fun e ↦ P.faceOf e = P.faceOf d) =
      (P.faceBoundary d).toFinset := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
      P.mem_faceBoundary_iff]
    constructor
    · intro h
      exact (Quotient.exact h).symm
    · intro h
      exact Quotient.sound h.symm
  have hcard : (Finset.univ.filter (fun e ↦ P.faceOf e = P.faceOf d)).card =
      (P.faceBoundary d).length := by
    rw [hset, List.toFinset_card_of_nodup (P.faceBoundary_nodup d)]
  simpa only [incidenceDegree, vertexOf, faceOf] using hcard

/-- The cycle of a dart under edge reversal consists of exactly that dart and its mate. -/
theorem edge_sameCycle_iff [Finite D] (d e : D) :
    P.edge.SameCycle d e ↔ e = d ∨ e = P.edge d := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp : ∀ k : ℕ, (P.edge ^ k) d = d ∨ (P.edge ^ k) d = P.edge d := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with ih | ih
        · rw [ih]
          exact Or.inr rfl
        · rw [ih, P.edge_involutive]
          exact Or.inl rfl
    simpa [hn] using hp n
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)

/-- Equality of actual edges has the expected two-dart characterization. -/
theorem edgeOf_eq_iff [Finite D] (d e : D) :
    P.edgeOf e = P.edgeOf d ↔ e = d ∨ e = P.edge d := by
  constructor
  · intro h
    exact (P.edge_sameCycle_iff d e).mp (Quotient.exact h).symm
  · intro h
    exact Quotient.sound ((P.edge_sameCycle_iff d e).mpr h).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every actual ribbon edge has exactly two incidence darts, also when it is a loop. -/
theorem edge_incidenceDegree [Fintype D] (e : P.Edge) : incidenceDegree P.edgeOf e = 2 := by
  classical
  induction e using Quotient.inductionOn with
  | h d =>
    have hset : Finset.univ.filter (fun e ↦ P.edgeOf e = P.edgeOf d) = {d, P.edge d} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, P.edgeOf_eq_iff]
    have hcard : (Finset.univ.filter (fun e ↦ P.edgeOf e = P.edgeOf d)).card = 2 := by
      rw [hset]
      exact Finset.card_pair (Ne.symm (P.edge_ne d))
    unfold incidenceDegree
    simpa only [incidenceDegree, edgeOf] using hcard

/-- The actual edge quotient has half as many elements as the dart type. -/
theorem card_darts [Fintype D] : Fintype.card D = 2 * Fintype.card P.Edge :=
  card_darts_eq_twice_edges P.edgeOf P.edge_incidenceDegree

/-- Bridge surgery preserves the number of actual edges. -/
theorem bridge_card_edges [Fintype D] (a b : D) :
    Fintype.card (P.bridge a b).Edge = Fintype.card P.Edge := by
  have h := P.card_darts
  have hb := (P.bridge a b).card_darts
  omega

/-- Bridge surgery leaves the vertex cycles literally unchanged. -/
theorem bridge_card_vertices [Finite D] (a b : D) :
    Fintype.card (P.bridge a b).Vertex = Fintype.card P.Vertex := rfl

/-- Apply the spherical `C(6)` obstruction to the actual cycles of a ribbon map.
The Euler equation and degree bounds must be established by the geometric reduction argument. -/
theorem sphere_c6_impossible [Fintype D] (outside : P.Face)
    (hvertex : ∀ v, 6 ≤ incidenceDegree P.vertexOf v)
    (hface : ∀ f, f ≠ outside → 3 ≤ incidenceDegree P.faceOf f)
    (heuler : Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) : False :=
  Geometry.sphere_c6_impossible P.vertexOf P.edgeOf P.faceOf outside
    P.edge_incidenceDegree hvertex hface heuler

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
