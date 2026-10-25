module

public import SmallPresentation.SmallCancellationGeometryBoundaryOneVertex

/-!
# The nonabelian boundary theorem for spherical ribbon diagrams

If every vertex except a distinguished boundary vertex reads a relation in a group,
the boundary vertex reads a relation too. Contract an edge joining the boundary vertex
to another vertex, preserving its complete ordered word, until the one-vertex theorem
applies. No commutativity, freely chosen planar realization, or diagram axiom is assumed.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles
universe u
variable {K : Type*} [Group K]

/-- The boundary consequence of a finite planar diagram over an arbitrary group. -/
theorem boundary_product_one (D : Type u) [Fintype D] (P : RibbonMap D) (w : D → K)
    (he : ∀ d, w (P.edge d) = (w d)⁻¹)
    (hc : P.Connected) (hE : P.EulerEquality) (boundary : D)
    (hint : ∀ d, ¬P.rotation.SameCycle boundary d →
      ((P.vertexBoundary d).map w).prod = 1) :
    ((P.vertexBoundary boundary).map w).prod = 1 := by
  classical
  by_cases hx : ∃ a, P.rotation.SameCycle boundary a ∧
      ¬P.rotation.SameCycle boundary (P.edge a)
  · obtain ⟨a, hba, hbn⟩ := hx
    have hn : ¬P.rotation.SameCycle a (P.edge a) := fun h ↦ hbn (hba.trans h)
    have hnc : ¬P.rotation.SameCycle (P.rotation a) (P.edge a) := by
      simpa only [Equiv.Perm.sameCycle_apply_left] using hn
    let S := P.edgeSplice a
    let C := P.spliceCancellation a
    have hinv : w C.left * w C.right = 1 := by
      change w a * w (P.edge a) = 1
      rw [he, mul_inv_cancel]
    have haS : S.rotation.SameCycle a (P.rotation a) :=
      sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc
        (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    have habS : S.rotation.SameCycle a (P.edge a) :=
      haS.trans (cutAt_sameCycle_of_not_sameCycle P.rotation _ _ hnc)
    have hother : cycleProduct P.rotation w (P.edge a) = 1 := hint _ hbn
    by_cases hs : ∃ c : P.ContractDart a, S.rotation.SameCycle a c.val
    · obtain ⟨c, hsc⟩ := hs
      have hsmall : ((P.contractEdge a).vertexBoundary c |>.map (fun d ↦ w d.val)).prod = 1 := by
        apply boundary_product_one (P.ContractDart a) (P.contractEdge a) (fun d ↦ w d.val)
          ?_ (P.contractEdge_connected hc a hn) (P.contractEdge_euler a hn hE) c ?_
        · intro d
          rw [P.contractEdge_edge_val]
          exact he d.val
        · intro d hd
          have hsd : ¬S.rotation.SameCycle c.val d.val := by
            intro h
            exact hd ((P.contractEdge_sameVertex_iff a c d).mpr h)
          have hda : ¬P.rotation.SameCycle d.val (P.rotation a) := by
            intro h
            have hh := sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h
            exact hsd (hsc.symm.trans (haS.trans hh.symm))
          have hdb : ¬P.rotation.SameCycle d.val (P.edge a) := by
            intro h
            have hh := sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h
            exact hsd (hsc.symm.trans (habS.trans hh.symm))
          have hb : ¬P.rotation.SameCycle boundary d.val := by
            intro h
            apply hda
            exact (h.symm.trans hba).trans
              (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
          rw [show ((P.contractEdge a).vertexBoundary d |>.map (fun e ↦ w e.val)).prod =
              ((S.vertexBoundary d.val).map w).prod from C.vertex_product w hinv d]
          change cycleProduct (cutAt P.rotation (P.rotation a) (P.edge a)) w d.val = 1
          rw [cycleProduct_cutAt_unchanged P.rotation w _ _ _ hda hdb]
          exact hint _ hb
      have hvalue : cycleProduct S.rotation w c.val = 1 := by
        exact (C.vertex_product w hinv c).symm.trans hsmall
      have hmerge : cycleProduct S.rotation w (P.rotation a) = 1 :=
        (cycleProduct_eq_one_of_sameCycle S.rotation w (hsc.symm.trans haS)).mp hvalue
      change cycleProduct (cutAt P.rotation (P.rotation a) (P.edge a)) w (P.rotation a) = 1 at hmerge
      rw [cycleProduct_cutAt_merge P.rotation w _ _ hnc, hother, mul_one] at hmerge
      exact (cycleProduct_eq_one_of_sameCycle P.rotation w
        (hba.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)))).mpr hmerge
    · have only (d : D) (hd : S.rotation.SameCycle a d) : d = a ∨ d = P.edge a := by
        by_contra hh
        push Not at hh
        exact hs ⟨⟨d, hh⟩, hd⟩
      have hfa : P.rotation a = a := by
        rcases only (P.rotation a) haS with h | h
        · exact h
        · have hh : P.rotation.SameCycle a (P.rotation a) :=
            Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
          rw [h] at hh
          exact False.elim (hn hh)
      have hfb : P.rotation (P.edge a) = P.edge a := by
        have hh : S.rotation.SameCycle (P.edge a) (P.rotation (P.edge a)) :=
          sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc
            (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
        rcases only (P.rotation (P.edge a)) (habS.trans hh) with h | h
        · have hv₀ : P.rotation.SameCycle (P.edge a) (P.rotation (P.edge a)) :=
            Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
          have hv : P.rotation.SameCycle (P.edge a) a := by
            simpa only [h] using hv₀
          exact False.elim (hn hv.symm)
        · exact h
      have product_fixed (d : D) (hd : P.rotation d = d) :
          cycleProduct P.rotation w d = w d := by
        have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hd
        simp [cycleProduct, cycleBoundary, hp, List.ofFn_succ]
      rw [product_fixed _ hfb, he, inv_eq_one] at hother
      have haone : cycleProduct P.rotation w a = 1 := (product_fixed _ hfa).trans hother
      exact (cycleProduct_eq_one_of_sameCycle P.rotation w hba).mpr haone
  · have hedge (d : D) : P.rotation.SameCycle boundary (P.edge d) ↔
        P.rotation.SameCycle boundary d := by
      have hclosed : ∀ e, P.rotation.SameCycle boundary e →
          P.rotation.SameCycle boundary (P.edge e) := by
        intro e h
        by_contra hn
        exact hx ⟨e, h, hn⟩
      constructor
      · intro h
        simpa only [P.edge_involutive d] using hclosed (P.edge d) h
      · exact hclosed d
    have hv (d : D) : P.rotation.SameCycle boundary d :=
      (P.invariant_on_component (P.rotation.SameCycle boundary) hedge
        (fun d ↦ Equiv.Perm.sameCycle_apply_right) (hc boundary d)).mp (.refl _ _)
    exact one_vertex_product_one D P w he (fun d e ↦ (hv d).symm.trans (hv e)) hE boundary
termination_by Fintype.card D
decreasing_by
  exact (P.spliceCancellation a).card_darts_lt

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
