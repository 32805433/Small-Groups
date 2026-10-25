module

public import SmallPresentation.SmallCancellationGeometryEdgeContractionTopology

/-! Choose a contraction incident to a marked boundary vertex, including the last-edge case. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} (P : RibbonMap D)

/-- A proper marked vertex in a connected graph has an edge leaving that vertex. -/
theorem exists_edge_leaving_vertex (hc : P.Connected) (b : D)
    (hn : ¬∀ d, P.rotation.SameCycle b d) :
    ∃ a, P.rotation.SameCycle b a ∧ ¬P.rotation.SameCycle b (P.edge a) := by
  classical
  by_contra h
  push Not at h
  apply hn
  intro d
  apply (P.invariant_on_component (fun x ↦ P.rotation.SameCycle b x) ?_ ?_ (hc b d)).mp
    (.refl _ _)
  · intro x
    constructor
    · intro hx
      have hh := h (P.edge x) hx
      simpa only [P.edge_involutive x] using hh
    · exact h x
  · intro x
    exact Equiv.Perm.sameCycle_apply_right

/-- The selected exit edge really joins distinct vertex cycles. -/
theorem distinct_vertex_of_exit (b a : D) (ha : P.rotation.SameCycle b a)
    (he : ¬P.rotation.SameCycle b (P.edge a)) :
    ¬P.rotation.SameCycle a (P.edge a) := fun h ↦ he (ha.trans h)

/-- If the merged vertex has no surviving incidence, both original endpoint vertices were
singletons. This is the only degenerate contraction case in a connected ribbon. -/
theorem endpoints_fixed_of_no_merged_survivor (a : D)
    (hn : ¬P.rotation.SameCycle a (P.edge a))
    (hno : ∀ d : P.ContractDart a,
      ¬(P.rotation.SameCycle d.val a ∨ P.rotation.SameCycle d.val (P.edge a))) :
    P.rotation a = a ∧ P.rotation (P.edge a) = P.edge a := by
  have h₁ : P.rotation a = a := by
    by_contra he
    have hb : P.rotation a ≠ P.edge a := by
      intro hh
      apply hn
      rw [← hh]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    exact hno ⟨P.rotation a, he, hb⟩ (Or.inl
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)))
  have h₂ : P.rotation (P.edge a) = P.edge a := by
    by_contra he
    have ha : P.rotation (P.edge a) ≠ a := by
      intro hh
      have hs : P.rotation.SameCycle (P.rotation (P.edge a)) (P.edge a) :=
        Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)
      exact hn (by simpa only [hh] using hs)
    exact hno ⟨P.rotation (P.edge a), ha, he⟩ (Or.inr
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)))
  exact ⟨h₁, h₂⟩

/-- In a connected ribbon, a contraction with no merged survivor exhausts the graph. -/
theorem edge_exhausts_of_no_merged_survivor (hc : P.Connected) (a : D)
    (hn : ¬P.rotation.SameCycle a (P.edge a))
    (hno : ∀ d : P.ContractDart a,
      ¬(P.rotation.SameCycle d.val a ∨ P.rotation.SameCycle d.val (P.edge a))) (d : D) :
    d = a ∨ d = P.edge a := by
  obtain ⟨h₁, h₂⟩ := P.endpoints_fixed_of_no_merged_survivor a hn hno
  exact P.isolated_edge_component a h₁ h₂ (hc a d)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
