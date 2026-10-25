module

public import SmallPresentation.SmallCancellationGeometryMarkedNormalization

/-! Monogons at a marked two-incidence vertex force an isolated component. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} [Finite D] (P : RibbonMap D)

omit [Finite D] in
/-- A nontrivial two-cycle has the literal displayed boundary. -/
theorem vertexBoundary_two_cycle (a : D) (hne : a ≠ P.rotation a)
    (ht : P.rotation (P.rotation a) = a) :
    P.vertexBoundary a = [a, P.rotation a] := by
  let C : AdjacentCancellation P := ⟨a, P.rotation a, hne, rfl⟩
  exact C.vertexBoundary_of_two_cycle ht

/-- A monogon incident to a vertex of degree two isolates that vertex's two darts. -/
theorem monogon_two_cycle_component (a : D) (hne : a ≠ P.rotation a)
    (ht : P.rotation (P.rotation a) = a) (d : D) (hd : P.rotation.SameCycle a d)
    (hf : P.face d = d) (e : D) (he : P.SameComponent a e) :
    P.rotation.SameCycle a e := by
  have hed : P.edge d = P.rotation d := by
    have hh := congrArg P.rotation hf
    simpa only [face_apply, Equiv.apply_symm_apply] using hh
  have hmem : d ∈ P.vertexBoundary a := (P.mem_vertexBoundary_iff a d).mpr hd
  rw [P.vertexBoundary_two_cycle a hne ht] at hmem
  have hea : P.edge a = P.rotation a := by
    rcases List.mem_cons.mp hmem with h | h
    · simpa only [h] using hed
    · have hd' : d = P.rotation a := by simpa only [List.mem_singleton] using h
      have hb : P.edge (P.rotation a) = a := by simpa only [hd', ht] using hed
      have hh := congrArg P.edge hb
      simpa only [P.edge_involutive (P.rotation a)] using hh.symm
  rcases P.isolated_two_dart_component a (P.rotation a) hea rfl ht he with h | h
  · rw [h]
  · rw [h]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- An exceptional two-marker vertex cannot support a monogon in a connected picture
that also contains another vertex. No cyclic-reduction hypothesis at the marked vertex is used. -/
theorem no_monogon_at_two_cycle (hc : P.Connected) (a : D) (hne : a ≠ P.rotation a)
    (ht : P.rotation (P.rotation a) = a) (other : D)
    (hother : ¬P.rotation.SameCycle a other) (d : D) (hd : P.rotation.SameCycle a d) :
    P.face d ≠ d := by
  intro hf
  exact hother (P.monogon_two_cycle_component a hne ht d hd hf other (hc _ _))

/-- The marked-vertex monogon exclusion only requires degree at most two; in particular
it remains valid after a compression that shortens the marked vertex boundary. -/
theorem no_monogon_at_small_vertex (hc : P.Connected) (a : D)
    (hsize : (P.vertexBoundary a).length ≤ 2) (other : D)
    (hother : ¬P.rotation.SameCycle a other) (d : D) (hd : P.rotation.SameCycle a d) :
    P.face d ≠ d := by
  intro hf
  have hed : P.edge d = P.rotation d := by
    have hh := congrArg P.rotation hf
    simpa only [face_apply, Equiv.apply_symm_apply] using hh
  have hn : P.rotation d ≠ d := fun h ↦ P.edge_ne d (hed.trans h)
  have hpd : Function.minimalPeriod P.rotation d = Function.minimalPeriod P.rotation a := by
    obtain ⟨n, he⟩ := hd.exists_nat_pow_eq
    rw [← he]
    exact Function.minimalPeriod_apply_iterate (P.rotation.injective.mem_periodicPts a) n
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts
    (P.rotation.injective.mem_periodicPts d)
  have hnot : Function.minimalPeriod P.rotation d ≠ 1 := by
    intro h
    exact hn (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
  have htwo : Function.minimalPeriod P.rotation d = 2 := by
    rw [vertexBoundary_length] at hsize
    omega
  have ht : P.rotation (P.rotation d) = d := by
    have hh := Function.iterate_minimalPeriod (f := P.rotation) (x := d)
    rw [htwo] at hh
    exact hh
  exact P.no_monogon_at_two_cycle hc d hn.symm ht other
    (fun h ↦ hother (hd.trans h)) d (.refl _ _) hf

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
