module

public import SmallPresentation.SmallCancellationGeometryVertexCut

/-!
# Exact component accounting for a corridor cut

If two cut positions remain connected after the cut, the old component set is unchanged.
Otherwise the old component set is the new set with the two distinguished components
identified. The explicit equivalence below proves that exactly one extra component appears;
it does not assume that cutting preserves connectedness.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

attribute [local instance] Classical.propDecidable

variable {D : Type*} (P : RibbonMap D)

def componentClass (d : D) : P.Component := Quotient.mk _ d

theorem componentClass_eq_iff (d e : D) :
    P.componentClass d = P.componentClass e ↔ P.SameComponent d e := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; apply Quotient.sound; exact h

@[simp] theorem componentClass_edge (d : D) :
    P.componentClass (P.edge d) = P.componentClass d :=
  Quotient.sound (Relation.EqvGen.symm _ _ (P.component_edge d))

@[simp] theorem componentClass_rotation (d : D) :
    P.componentClass (P.rotation d) = P.componentClass d :=
  Quotient.sound (Relation.EqvGen.symm _ _ (P.component_rotation d))

variable (a b : D)

abbrev CutComponent := (P.vertexCut a b).Component

noncomputable def cutCollapseClass
    (hnew : ¬ (P.vertexCut a b).SameComponent a b) (c : P.CutComponent a b) :
    {c : P.CutComponent a b // c ≠ (P.vertexCut a b).componentClass b} := by
  classical
  exact if h : c = (P.vertexCut a b).componentClass b then
    ⟨(P.vertexCut a b).componentClass a, fun he ↦ hnew (Quotient.exact he)⟩ else ⟨c, h⟩

theorem cutCollapseClass_a_b (hnew : ¬ (P.vertexCut a b).SameComponent a b) :
    P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass a) =
      P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass b) := by
  classical
  have hn : (P.vertexCut a b).componentClass a ≠ (P.vertexCut a b).componentClass b :=
    fun h ↦ hnew (((P.vertexCut a b).componentClass_eq_iff a b).mp h)
  simp [cutCollapseClass, hn]

theorem cutCollapseClass_swap (hnew : ¬ (P.vertexCut a b).SameComponent a b) (d : D) :
    P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass (Equiv.swap a b d)) =
      P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass d) := by
  classical
  by_cases ha : d = a
  · subst d
    rw [Equiv.swap_apply_left]
    exact (P.cutCollapseClass_a_b a b hnew).symm
  by_cases hb : d = b
  · subst d
    rw [Equiv.swap_apply_right]
    exact P.cutCollapseClass_a_b a b hnew
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem cutCollapseClass_rotation (hnew : ¬ (P.vertexCut a b).SameComponent a b) (d : D) :
    P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass (P.rotation d)) =
      P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass d) := by
  have h := congrArg (P.cutCollapseClass a b hnew)
    ((P.vertexCut a b).componentClass_rotation d)
  change P.cutCollapseClass a b hnew
    ((P.vertexCut a b).componentClass (Equiv.swap a b (P.rotation d))) = _ at h
  rw [P.cutCollapseClass_swap] at h
  exact h

theorem cutCollapseClass_constant (hnew : ¬ (P.vertexCut a b).SameComponent a b)
    {d e : D} (h : P.SameComponent d e) :
    P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass d) =
      P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass e) := by
  induction h with
  | rel x y h =>
    rcases h with h | h
    · rw [← h]
      change _ = P.cutCollapseClass a b hnew
        ((P.vertexCut a b).componentClass ((P.vertexCut a b).edge x))
      rw [componentClass_edge]
    · rw [← h]
      exact (P.cutCollapseClass_rotation a b hnew x).symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def componentsToCutMinus
    (hnew : ¬ (P.vertexCut a b).SameComponent a b) :
    P.Component → {c : P.CutComponent a b // c ≠ (P.vertexCut a b).componentClass b} :=
  Quotient.lift (fun d ↦ P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass d))
    (fun _ _ h ↦ P.cutCollapseClass_constant a b hnew h)

def cutComponentsToOld (hold : P.SameComponent a b) : P.CutComponent a b → P.Component :=
  Quotient.map id (fun _ _ h ↦ P.vertexCut_component_refines a b hold h)

theorem cutComponentsToOld_collapse (hold : P.SameComponent a b)
    (hnew : ¬ (P.vertexCut a b).SameComponent a b) (c : P.CutComponent a b) :
    P.cutComponentsToOld a b hold (P.cutCollapseClass a b hnew c).val =
      P.cutComponentsToOld a b hold c := by
  classical
  by_cases h : c = (P.vertexCut a b).componentClass b
  · subst c
    simp only [cutCollapseClass, dite_true, cutComponentsToOld]
    exact Quotient.sound hold
  · simp only [cutCollapseClass, dite_eq_right h]

/-- An actual split replaces exactly one old component by two new components. -/
noncomputable def vertexCutSplitComponentsEquiv (hold : P.SameComponent a b)
    (hnew : ¬ (P.vertexCut a b).SameComponent a b) :
    P.Component ≃ {c : P.CutComponent a b // c ≠ (P.vertexCut a b).componentClass b} where
  toFun := P.componentsToCutMinus a b hnew
  invFun c := P.cutComponentsToOld a b hold c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d => exact P.cutComponentsToOld_collapse a b hold hnew _
  right_inv c := by
    rcases c with ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h d =>
      apply Subtype.ext
      change (P.vertexCut a b).componentClass d ≠ (P.vertexCut a b).componentClass b at hc
      change (P.cutCollapseClass a b hnew ((P.vertexCut a b).componentClass d)).val = _
      simp only [cutCollapseClass, dite_eq_right hc]
      rfl

/-- If the cut points become disconnected, the number of components increases by one. -/
theorem vertexCut_card_components_split [Finite D] (hold : P.SameComponent a b)
    (hnew : ¬ (P.vertexCut a b).SameComponent a b)
    [Fintype P.Component] [Fintype (P.CutComponent a b)] :
    Fintype.card (P.CutComponent a b) = Fintype.card P.Component + 1 := by
  classical
  let := Fintype.ofFinite
    {c : P.CutComponent a b // c ≠ (P.vertexCut a b).componentClass b}
  have hc := Fintype.card_congr (P.vertexCutSplitComponentsEquiv a b hold hnew)
  have hp : 0 < Fintype.card (P.CutComponent a b) :=
    Fintype.card_pos_iff.mpr ⟨(P.vertexCut a b).componentClass a⟩
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at hc
  omega

/-- A cut inside one component preserves its count or adds precisely one component. -/
theorem vertexCut_card_components [Finite D] (hold : P.SameComponent a b)
    [Fintype P.Component] [Fintype (P.CutComponent a b)] :
    Fintype.card (P.CutComponent a b) = Fintype.card P.Component ∨
      Fintype.card (P.CutComponent a b) = Fintype.card P.Component + 1 := by
  classical
  by_cases hnew : (P.vertexCut a b).SameComponent a b
  · exact Or.inl (Fintype.card_congr (P.vertexCutComponentsEquiv a b hold hnew))
  · exact Or.inr (P.vertexCut_card_components_split a b hold hnew)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
