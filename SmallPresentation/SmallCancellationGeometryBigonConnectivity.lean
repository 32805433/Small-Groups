module

public import SmallPresentation.SmallCancellationGeometryBigon
public import SmallPresentation.SmallCancellationGeometryComponents

/-!
# Connectivity under actual bigon suppression

The removed darts retract to their preceding surviving darts. Each old edge or vertex step
maps to a path of the suppressed ribbon. Thus suppression preserves connectivity without an
extra topological assumption.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D : Type*} {P : RibbonMap D} (B : Bigon P)

def leftDart : B.Dart := ⟨B.left, (P.edge_ne B.left).symm, B.left_ne_mate_right⟩

def rightDart : B.Dart := ⟨B.right, B.mate_left_ne_right.symm, (P.edge_ne B.right).symm⟩

/-- Retract each removed endpoint to its predecessor in the old vertex rotation. -/
noncomputable def collapse (d : D) : B.Dart := by
  classical
  exact if h₁ : d = P.edge B.left then B.rightDart
    else if h₂ : d = P.edge B.right then B.leftDart else ⟨d, h₁, h₂⟩

@[simp] theorem collapse_survivor (d : B.Dart) : B.collapse d.val = d := by
  classical
  simp only [collapse, dite_eq_right d.property.1, dite_eq_right d.property.2]

@[simp] theorem collapse_mate_left : B.collapse (P.edge B.left) = B.rightDart := by
  classical
  simp [collapse]

@[simp] theorem collapse_mate_right : B.collapse (P.edge B.right) = B.leftDart := by
  classical
  simp [collapse, B.mate_ne.symm]

@[simp] theorem collapse_left : B.collapse B.left = B.leftDart :=
  B.collapse_survivor B.leftDart

@[simp] theorem collapse_right : B.collapse B.right = B.rightDart :=
  B.collapse_survivor B.rightDart

@[simp] theorem edge_leftDart : B.edge B.leftDart = B.rightDart := by
  apply Subtype.ext
  exact B.bridged_edge_left

@[simp] theorem edge_rightDart : B.edge B.rightDart = B.leftDart := by
  apply Subtype.ext
  exact B.bridged_edge_right

/-- The edge step descends exactly under the retraction. -/
theorem collapse_edge (d : D) : B.collapse (P.edge d) = B.edge (B.collapse d) := by
  classical
  by_cases h₁ : d = P.edge B.left
  · subst d; rw [P.edge_involutive B.left, B.collapse_left, B.collapse_mate_left,
      B.edge_rightDart]
  by_cases h₂ : d = P.edge B.right
  · subst d; rw [P.edge_involutive B.right, B.collapse_right, B.collapse_mate_right,
      B.edge_leftDart]
  let s : B.Dart := ⟨d, h₁, h₂⟩
  change B.collapse (P.edge s.val) = B.edge (B.collapse s.val)
  rw [B.collapse_survivor]
  by_cases hl : d = B.left
  · subst d; rw [B.collapse_mate_left]
    exact (B.edge_leftDart).symm
  by_cases hr : d = B.right
  · subst d; rw [B.collapse_mate_right]
    exact (B.edge_rightDart).symm
  have he₁ : P.edge d ≠ P.edge B.left := P.edge.injective.ne hl
  have he₂ : P.edge d ≠ P.edge B.right := P.edge.injective.ne hr
  have hes : B.collapse (P.edge s.val) = ⟨P.edge d, he₁, he₂⟩ :=
    B.collapse_survivor ⟨P.edge d, he₁, he₂⟩
  rw [hes]
  apply Subtype.ext
  change P.edge d = B.bridged.edge d
  exact (P.bridge_edge_unchanged (P.edge B.left) B.right d h₁ hr he₁
    (fun h ↦ h₂ ((P.edge_involutive d).symm.trans (congrArg P.edge h)))).symm

/-- Removed endpoint successors survive, as witnessed by the actual new rotation. -/
theorem rotation_leftDart_val : (B.rotation B.leftDart).val = P.rotation (P.edge B.right) := by
  classical
  rw [B.rotation_val]
  simp only [leftDart, ite_true]

theorem rotation_rightDart_val : (B.rotation B.rightDart).val = P.rotation (P.edge B.left) := by
  classical
  rw [B.rotation_val]
  simp only [rightDart, B.left_ne_right.symm, ite_false, ite_true]

/-- An old vertex step either collapses to a point or becomes one new vertex step. -/
theorem collapse_rotation (d : D) :
    B.collapse (P.rotation d) = B.collapse d ∨
      B.collapse (P.rotation d) = B.rotation (B.collapse d) := by
  classical
  by_cases hl : d = B.left
  · subst d
    exact Or.inl (by rw [B.rotation_left, B.collapse_mate_right, B.collapse_left])
  by_cases hr : d = B.right
  · subst d
    exact Or.inl (by rw [B.rotation_right, B.collapse_mate_left, B.collapse_right])
  right
  by_cases h₁ : d = P.edge B.left
  · subst d
    rw [B.collapse_mate_left, ← B.rotation_rightDart_val, B.collapse_survivor]
  by_cases h₂ : d = P.edge B.right
  · subst d
    rw [B.collapse_mate_right, ← B.rotation_leftDart_val, B.collapse_survivor]
  let s : B.Dart := ⟨d, h₁, h₂⟩
  have hs : (B.rotation s).val = P.rotation d := by
    rw [B.rotation_val]
    exact by simp only [s, hl, hr, ite_false]
  change B.collapse (P.rotation d) = B.rotation (B.collapse s.val)
  rw [B.collapse_survivor, ← hs, B.collapse_survivor]

/-- The actual old component relation descends along suppression. -/
theorem collapse_sameComponent {d e : D} (h : P.SameComponent d e) :
    B.suppress.SameComponent (B.collapse d) (B.collapse e) := by
  apply P.map_components B.suppress B.collapse ?_ ?_ h
  · intro x
    rw [B.collapse_edge]
    exact B.suppress.component_edge _
  · intro x
    rcases B.collapse_rotation x with hx | hx
    · rw [hx]; exact Relation.EqvGen.refl _
    · rw [hx]; exact B.suppress.component_rotation _

/-- Bigon suppression of a connected ribbon is connected. -/
theorem connected (hc : P.Connected) : B.suppress.Connected := by
  intro d e
  simpa only [B.collapse_survivor] using B.collapse_sameComponent (hc d.val e.val)

/-- Retraction stays in the original connected component. -/
theorem component_collapse (d : D) : P.SameComponent d (B.collapse d).val := by
  classical
  by_cases h₁ : d = P.edge B.left
  · subst d
    rw [B.collapse_mate_left]
    change P.SameComponent (P.edge B.left) B.right
    rw [← B.rotation_right]
    exact Relation.EqvGen.symm _ _ (P.component_rotation _)
  by_cases h₂ : d = P.edge B.right
  · subst d
    rw [B.collapse_mate_right]
    change P.SameComponent (P.edge B.right) B.left
    rw [← B.rotation_left]
    exact Relation.EqvGen.symm _ _ (P.component_rotation _)
  change P.SameComponent d (B.collapse (⟨d, h₁, h₂⟩ : B.Dart).val).val
  rw [B.collapse_survivor]
  exact Relation.EqvGen.refl _

/-- Inclusion of surviving darts sends every new component into an old component. -/
theorem include_sameComponent {d e : B.Dart} (h : B.suppress.SameComponent d e) :
    P.SameComponent d.val e.val := by
  apply B.suppress.map_components P Subtype.val ?_ ?_ h
  · intro x
    have hc := Relation.EqvGen.trans _ _ _ (P.component_edge x.val)
      (B.component_collapse (P.edge x.val))
    rw [B.collapse_edge, B.collapse_survivor] at hc
    exact hc
  · intro x
    change P.SameComponent x.val (B.rotation x).val
    rw [B.rotation_val]
    split_ifs with hl hr
    · rw [hl, ← B.rotation_left]
      exact Relation.EqvGen.trans _ _ _ (P.component_rotation B.left)
        (P.component_rotation (P.rotation B.left))
    · rw [hr, ← B.rotation_right]
      exact Relation.EqvGen.trans _ _ _ (P.component_rotation B.right)
        (P.component_rotation (P.rotation B.right))
    · exact P.component_rotation _

/-- Suppression preserves the exact set of connected components. -/
noncomputable def componentsEquiv : B.suppress.Component ≃ P.Component where
  toFun := Quotient.map Subtype.val (fun _ _ h ↦ B.include_sameComponent h)
  invFun := Quotient.map B.collapse (fun _ _ h ↦ B.collapse_sameComponent h)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ d =>
      change Quotient.mk _ (B.collapse d.val) = Quotient.mk _ d
      rw [B.collapse_survivor]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ d =>
      apply Quotient.sound
      exact Relation.EqvGen.symm _ _ (B.component_collapse d)

theorem connected_iff : B.suppress.Connected ↔ P.Connected := by
  constructor
  · intro hc d e
    exact Relation.EqvGen.trans _ _ _ (B.component_collapse d)
      (Relation.EqvGen.trans _ _ _ (B.include_sameComponent (hc _ _))
        (Relation.EqvGen.symm _ _ (B.component_collapse e)))
  · exact B.connected

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
