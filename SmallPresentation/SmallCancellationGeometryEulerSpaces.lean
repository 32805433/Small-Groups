module

public import SmallPresentation.SmallCancellationGeometryComponents
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rational function spaces on ribbon incidences

Functions fixed by a permutation are exactly functions on its actual cycle quotient.
For a fixed-point-free edge involution, antisymmetric dart functions have dimension equal
to the number of edges. These statements do not assume a planar embedding.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open Module

variable {D : Type*}

/-- Rational dart functions constant on the cycles of a permutation. -/
def fixedSpace (σ : Equiv.Perm D) : Submodule ℚ (D → ℚ) where
  carrier := {f | ∀ d, f (σ d) = f d}
  zero_mem' := fun _ ↦ rfl
  add_mem' := by intro f g hf hg d; simp only [Pi.add_apply, hf d, hg d]
  smul_mem' := by intro c f hf d; simp only [Pi.smul_apply, hf d]

/-- Pull back a function on actual cycles to the dart set. -/
noncomputable def fixedSpaceEquiv [Finite D] (σ : Equiv.Perm D) :
    (PermutationCycles.Cycles σ → ℚ) ≃ₗ[ℚ] fixedSpace σ where
  toFun f := ⟨fun d ↦ f (PermutationCycles.cycle σ d),
    fun d ↦ congrArg f (PermutationCycles.cycle_apply σ d)⟩
  invFun f := Quotient.lift f.val (fun _ _ h ↦
    PermutationCycles.constant_on_cycles σ f.val f.property h)
  left_inv f := by funext c; induction c using Quotient.inductionOn with | _ d => rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_fixedSpace [Finite D] (σ : Equiv.Perm D)
    [Fintype (PermutationCycles.Cycles σ)] :
    finrank ℚ (fixedSpace σ) = Fintype.card (PermutationCycles.Cycles σ) := by
  rw [← (fixedSpaceEquiv σ).finrank_eq, Module.finrank_fintype_fun_eq_card]

variable (P : RibbonMap D)

/-- Antisymmetric edge functions retain one signed value for each edge. -/
def edgeSpace : Submodule ℚ (D → ℚ) where
  carrier := {f | ∀ d, f (P.edge d) = -f d}
  zero_mem' := by intro d; simp
  add_mem' := by intro f g hf hg d; simp only [Pi.add_apply, hf d, hg d, neg_add]
  smul_mem' := by intro c f hf d; simp only [Pi.smul_apply, hf d, smul_neg]

theorem fixed_edge_disjoint : Disjoint (fixedSpace P.edge) P.edgeSpace := by
  rw [Submodule.disjoint_def]
  intro f hf hg
  funext d
  have h₁ := hf d
  have h₂ := hg d
  change f d = 0
  linarith

theorem fixed_edge_sup : fixedSpace P.edge ⊔ P.edgeSpace = ⊤ := by
  apply top_unique
  intro f _
  let even : D → ℚ := fun d ↦ (f d + f (P.edge d)) / 2
  let odd : D → ℚ := fun d ↦ (f d - f (P.edge d)) / 2
  have he : even ∈ fixedSpace P.edge := by
    intro d
    dsimp only [even]
    rw [P.edge_involutive d]
    ring
  have ho : odd ∈ P.edgeSpace := by
    intro d
    dsimp only [odd]
    rw [P.edge_involutive d]
    ring
  have hf : even + odd = f := by funext d; dsimp [even, odd]; ring
  rw [← hf]
  exact Submodule.add_mem_sup he ho

/-- Antisymmetric dart functions have exactly one dimension per actual edge. -/
theorem finrank_edgeSpace [Fintype D] : finrank ℚ P.edgeSpace = Fintype.card P.Edge := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace P.edge) P.edgeSpace
  rw [P.fixed_edge_sup, P.fixed_edge_disjoint.eq_bot, finrank_top, finrank_bot,
    add_zero, Module.finrank_fintype_fun_eq_card, finrank_fixedSpace] at h
  have he := P.card_darts
  change Fintype.card D = 2 * Fintype.card P.Edge at he
  change Fintype.card D = Fintype.card P.Edge + finrank ℚ P.edgeSpace at h
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
