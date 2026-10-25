module

public import SmallPresentation.SmallCancellationGeometryEulerSpaces

/-!
# Vertex and face gradients on a finite ribbon map

Both gradients take values in antisymmetric edge functions. Their kernels are exactly the
functions on actual connected components, so rank-nullity gives the two combinatorial ranks.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open Module

variable {D : Type*} (P : RibbonMap D)

noncomputable instance componentFintype [Finite D] : Fintype P.Component := Fintype.ofFinite _

/-- Functions invariant under both edge and vertex steps are constant on components. -/
theorem constant_on_component {B : Type*} (f : D → B)
    (he : ∀ d, f (P.edge d) = f d) (hr : ∀ d, f (P.rotation d) = f d)
    {d e : D} (h : P.SameComponent d e) : f d = f e := by
  induction h with
  | rel x y h =>
    rcases h with h | h
    · rw [← h, he]
    · rw [← h, hr]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Difference across the oriented edge, with a specified domain of invariant functions. -/
def gradient (σ : Equiv.Perm D) : fixedSpace σ →ₗ[ℚ] P.edgeSpace where
  toFun f := ⟨fun d ↦ f.val (P.edge d) - f.val d, by
    intro d
    change f.val (P.edge (P.edge d)) - f.val (P.edge d) =
      -(f.val (P.edge d) - f.val d)
    rw [P.edge_involutive d]
    ring⟩
  map_add' f g := by apply Subtype.ext; funext d; dsimp; ring
  map_smul' c f := by apply Subtype.ext; funext d; dsimp; ring

@[simp] theorem gradient_apply (σ : Equiv.Perm D) (f : fixedSpace σ) (d : D) :
    (P.gradient σ f).val d = f.val (P.edge d) - f.val d := rfl

theorem gradient_ker_iff (σ : Equiv.Perm D) (f : fixedSpace σ) :
    f ∈ (P.gradient σ).ker ↔ ∀ d, f.val (P.edge d) = f.val d := by
  constructor
  · intro h d
    have hh := congrArg (fun g : P.edgeSpace ↦ g.val d) h
    exact sub_eq_zero.mp hh
  · intro h
    apply Subtype.ext
    funext d
    exact sub_eq_zero.mpr (h d)

/-- A permutation whose steps generate the same components gives the same gradient kernel.
The two hypotheses express actual path containment and recovery of vertex invariance. -/
noncomputable def componentKernelEquiv (σ : Equiv.Perm D)
    (hstep : ∀ d, P.SameComponent d (σ d))
    (hrecover : ∀ f : fixedSpace σ, (∀ d, f.val (P.edge d) = f.val d) →
      ∀ d, f.val (P.rotation d) = f.val d) :
    (P.Component → ℚ) ≃ₗ[ℚ] (P.gradient σ).ker where
  toFun f := ⟨⟨fun d ↦ f (Quotient.mk _ d), fun d ↦
    congrArg f (Quotient.sound (Relation.EqvGen.symm _ _ (hstep d)))⟩,
      (P.gradient_ker_iff σ _).mpr (fun d ↦
        congrArg f (Quotient.sound (Relation.EqvGen.symm _ _ (P.component_edge d))))⟩
  invFun f := Quotient.lift f.val.val (fun _ _ h ↦
    P.constant_on_component f.val.val ((P.gradient_ker_iff σ f.val).mp f.property)
      (hrecover f.val ((P.gradient_ker_iff σ f.val).mp f.property)) h)
  left_inv f := by funext c; induction c using Quotient.inductionOn with | _ d => rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The kernel of the vertex gradient consists exactly of component functions. -/
noncomputable def vertexKernelEquiv :
    (P.Component → ℚ) ≃ₗ[ℚ] (P.gradient P.rotation).ker :=
  P.componentKernelEquiv P.rotation P.component_rotation (fun f _ ↦ f.property)

/-- Edge and face invariance imply vertex invariance. -/
theorem rotation_invariant_of_face (f : fixedSpace P.face)
    (he : ∀ d, f.val (P.edge d) = f.val d) (d : D) :
    f.val (P.rotation d) = f.val d := by
  have h := f.property (P.edge (P.rotation d))
  rw [face_apply, P.edge_involutive, Equiv.symm_apply_apply, he] at h
  exact h.symm

/-- The kernel of the face gradient also consists exactly of component functions. -/
noncomputable def faceKernelEquiv :
    (P.Component → ℚ) ≃ₗ[ℚ] (P.gradient P.face).ker :=
  P.componentKernelEquiv P.face P.component_face P.rotation_invariant_of_face

theorem vertex_gradient_rank [Fintype D] :
    finrank ℚ (P.gradient P.rotation).range + Fintype.card P.Component =
      Fintype.card P.Vertex := by
  have h := (P.gradient P.rotation).finrank_range_add_finrank_ker
  rw [← P.vertexKernelEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    finrank_fixedSpace] at h
  exact h

theorem face_gradient_rank [Fintype D] :
    finrank ℚ (P.gradient P.face).range + Fintype.card P.Component =
      Fintype.card P.Face := by
  have h := (P.gradient P.face).finrank_range_add_finrank_ker
  rw [← P.faceKernelEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    finrank_fixedSpace] at h
  exact h

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
