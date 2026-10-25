module

public import SmallPresentation.SmallCancellationGeometryCorridorCuts

/-!
# Finite sequences of actual vertex splits

The relation records genuine cuts of a permutation cycle, rather than a planarity assertion.
It is stable under relabelling and adding unaffected permutation summands. Each such sequence
preserves the sphere Euler equation, with the actual number of components accounted for.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D E B : Type*}

inductive SplitRefinement : Equiv.Perm D → Equiv.Perm D → Prop
  | refl (σ) : SplitRefinement σ σ
  | cut {σ τ} : SplitRefinement σ τ → (a b : D) → a ≠ b → τ.SameCycle a b →
      SplitRefinement σ (cutAt τ a b)

namespace SplitRefinement

theorem trans {σ τ κ : Equiv.Perm D} (h₁ : SplitRefinement σ τ)
    (h₂ : SplitRefinement τ κ) : SplitRefinement σ κ := by
  induction h₂ with
  | refl => exact h₁
  | cut h a b hn hc ih => exact .cut ih a b hn hc

theorem single (σ : Equiv.Perm D) (a b : D) (hn : a ≠ b) (hc : σ.SameCycle a b) :
    SplitRefinement σ (cutAt σ a b) := .cut (.refl σ) a b hn hc

end SplitRefinement

/-- Conjugate an actual permutation to a new dart type. -/
def transport (e : D ≃ E) (σ : Equiv.Perm D) : Equiv.Perm E :=
  e.symm.trans (σ.trans e)

@[simp] theorem transport_at (e : D ≃ E) (σ : Equiv.Perm D) (d : D) :
    transport e σ (e d) = e (σ d) := by simp [transport]

theorem transport_cut (e : D ≃ E) (σ : Equiv.Perm D) (a b : D) :
    transport e (cutAt σ a b) = cutAt (transport e σ) (e a) (e b) := by
  classical
  apply Equiv.ext
  intro x
  obtain ⟨d, rfl⟩ := e.surjective x
  simp only [transport_at, cutAt_apply, e.injective.map_swap]

theorem SplitRefinement.transport [Finite D] {σ τ : Equiv.Perm D}
    (h : SplitRefinement σ τ) (e : D ≃ E) :
    SplitRefinement (PermutationCycles.transport e σ) (PermutationCycles.transport e τ) := by
  induction h with
  | refl => exact .refl _
  | @cut τ h a b hn hc ih =>
    rw [transport_cut]
    apply SplitRefinement.cut ih (e a) (e b) (e.injective.ne hn)
    apply sameCycle_map_of_step τ (PermutationCycles.transport e τ) e ?_ hc
    intro d
    rw [← transport_at]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

theorem SplitRefinement.sum_left [Finite D] {σ τ : Equiv.Perm D}
    (h : SplitRefinement σ τ) (κ : Equiv.Perm E) :
    SplitRefinement (Equiv.sumCongr σ κ) (Equiv.sumCongr τ κ) := by
  induction h with
  | refl => exact .refl _
  | @cut τ h a b hn hc ih =>
    rw [← cutAt_sum]
    apply SplitRefinement.cut ih (Sum.inl a) (Sum.inl b) (fun h ↦ hn (Sum.inl.inj h))
    exact sameCycle_map_of_step τ (Equiv.sumCongr τ κ) Sum.inl
      (fun d ↦ Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) hc

theorem cutAt_sum_right (σ : Equiv.Perm D) (τ : Equiv.Perm E) (a b : E) :
    cutAt (Equiv.sumCongr σ τ) (Sum.inr a) (Sum.inr b) =
      Equiv.sumCongr σ (cutAt τ a b) := by
  classical
  apply Equiv.ext
  intro d
  rcases d with d | d <;>
    simp only [cutAt_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.swap_apply_def]
  · simp
  · split_ifs <;> simp_all

theorem SplitRefinement.sum_right [Finite E] {σ τ : Equiv.Perm E}
    (h : SplitRefinement σ τ) (κ : Equiv.Perm D) :
    SplitRefinement (Equiv.sumCongr κ σ) (Equiv.sumCongr κ τ) := by
  induction h with
  | refl => exact .refl _
  | @cut τ h a b hn hc ih =>
    rw [← cutAt_sum_right]
    apply SplitRefinement.cut ih (Sum.inr a) (Sum.inr b) (fun h ↦ hn (Sum.inr.inj h))
    exact sameCycle_map_of_step τ (Equiv.sumCongr κ τ) Sum.inr
      (fun d ↦ Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) hc

end SmallPresentationStatements.PermutationCycles

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D : Type*} [Fintype D] (P : RibbonMap D)

def withRotation (σ : Equiv.Perm D) : RibbonMap D where
  edge := P.edge
  edge_involutive := P.edge_involutive
  edge_ne := P.edge_ne
  rotation := σ

omit [Fintype D] in
@[simp] theorem withRotation_self : P.withRotation P.rotation = P := by cases P; rfl

/-- Every finite sequence of genuine vertex splits preserves the total sphere Euler equation. -/
theorem splitRefinement_preserves_euler {τ : Equiv.Perm D}
    (h : SplitRefinement P.rotation τ)
    (hplanar : Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) :
    Fintype.card (P.withRotation τ).Vertex + Fintype.card (P.withRotation τ).Face =
      Fintype.card (P.withRotation τ).Edge + 2 * Fintype.card (P.withRotation τ).Component := by
  induction h with
  | refl => simpa only [withRotation_self] using hplanar
  | @cut τ h a b hn hc ih =>
    exact (P.withRotation τ).vertexCut_preserves_euler a b hn hc ih

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
