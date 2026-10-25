module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Cycle quotients and insertion into a permutation

Inserting a new point in an existing cycle preserves the cycle quotient. Adding
one further fixed point adds exactly one cycle. The explicit cap permutation is
the face operation arising when an adjacent cancellation pair is inserted into
a boundary matching. No planarity or Euler hypothesis is used in this lemma.
-/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D E B : Type*}

/-- All cycles, including fixed points, of a permutation. -/
abbrev Cycles (σ : Equiv.Perm D) := Quotient (Equiv.Perm.SameCycle.setoid σ)

/-- The cycle containing a specified element. -/
def cycle (σ : Equiv.Perm D) (d : D) : Cycles σ := Quotient.mk _ d

@[simp] theorem cycle_apply (σ : Equiv.Perm D) (d : D) : cycle σ (σ d) = cycle σ d :=
  Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- Mapping each permutation step into a target cycle suffices to map entire cycles. -/
theorem sameCycle_map_of_step [Finite D] (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (f : D → E) (hstep : ∀ d, τ.SameCycle (f d) (f (σ d)))
    {d e : D} (h : σ.SameCycle d e) : τ.SameCycle (f d) (f e) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Equiv.Perm.SameCycle.refl _ _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (hstep _)

/-- A function unchanged by each step is constant on every actual cycle. -/
theorem constant_on_cycles [Finite D] (σ : Equiv.Perm D) (f : D → B)
    (hstep : ∀ d, f (σ d) = f d) {d e : D} (h : σ.SameCycle d e) : f d = f e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hstep]; exact ih

/-- Transport cycles through a bijection intertwining the actual permutation steps. -/
def conjugateEquiv [Finite D] [Finite E] (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (e : D ≃ E) (he : ∀ d, e (σ d) = τ (e d)) : Cycles σ ≃ Cycles τ :=
  Quotient.congr e (by
    intro d d'
    constructor
    · exact sameCycle_map_of_step σ τ e (fun d ↦ by
        rw [he]; exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    · intro h
      have hi : ∀ x, e.symm (τ x) = σ (e.symm x) := by
        intro x
        apply e.injective
        simp only [Equiv.apply_symm_apply, he]
      have hh := sameCycle_map_of_step τ σ e.symm (fun x ↦ by
        rw [hi]; exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) h
      change σ.SameCycle d d'
      simpa only [Equiv.symm_apply_apply] using hh)

/-- Insert `inr true` immediately before `p` in its cycle and leave `inr false` fixed. -/
noncomputable def capPerm (σ : Equiv.Perm D) (p : D) : Equiv.Perm (D ⊕ Bool) := by
  classical
  exact (Equiv.sumCongr σ (Equiv.refl Bool)).trans
    (Equiv.swap (Sum.inl p) (Sum.inr true))

@[simp] theorem capPerm_false (σ : Equiv.Perm D) (p : D) :
    capPerm σ p (Sum.inr false) = Sum.inr false := by
  classical
  simp [capPerm, Equiv.swap_apply_of_ne_of_ne]

@[simp] theorem capPerm_true (σ : Equiv.Perm D) (p : D) :
    capPerm σ p (Sum.inr true) = Sum.inl p := by
  classical
  simp [capPerm]

theorem capPerm_inl_eq (σ : Equiv.Perm D) (p d : D) (h : σ d = p) :
    capPerm σ p (Sum.inl d) = Sum.inr true := by
  classical
  simp [capPerm, h]

theorem capPerm_inl_ne (σ : Equiv.Perm D) (p d : D) (h : σ d ≠ p) :
    capPerm σ p (Sum.inl d) = Sum.inl (σ d) := by
  classical
  simp [capPerm, Equiv.swap_apply_of_ne_of_ne, h]

/-- Every old step is replaced by one or two cap-permutation steps. -/
theorem capPerm_old_step (σ : Equiv.Perm D) (p d : D) :
    (capPerm σ p).SameCycle (Sum.inl d) (Sum.inl (σ d)) := by
  by_cases h : σ d = p
  · have h₁ : (capPerm σ p).SameCycle (Sum.inl d) (Sum.inr true) := by
      rw [← capPerm_inl_eq σ p d h]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    have h₂ : (capPerm σ p).SameCycle (Sum.inr true) (Sum.inl p) := by
      rw [← capPerm_true σ p]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    exact h₁.trans (h ▸ h₂)
  · rw [← capPerm_inl_ne σ p d h]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- Collapse the inserted point into its old cycle; distinguish the new fixed point. -/
def capClass (σ : Equiv.Perm D) (p : D) : D ⊕ Bool → Option (Cycles σ)
  | Sum.inl d => some (cycle σ d)
  | Sum.inr true => some (cycle σ p)
  | Sum.inr false => none

theorem capClass_step (σ : Equiv.Perm D) (p : D) (d : D ⊕ Bool) :
    capClass σ p (capPerm σ p d) = capClass σ p d := by
  rcases d with d | b
  · by_cases h : σ d = p
    · rw [capPerm_inl_eq σ p d h]
      change some (cycle σ p) = some (cycle σ d)
      rw [← h, cycle_apply]
    · rw [capPerm_inl_ne σ p d h]
      change some (cycle σ (σ d)) = some (cycle σ d)
      rw [cycle_apply]
  · cases b <;> simp [capClass]

/-- The forward map on cycle quotients, obtained from the actual permutation. -/
noncomputable def capCycles [Finite D] (σ : Equiv.Perm D) (p : D) :
    Cycles (capPerm σ p) → Option (Cycles σ) :=
  Quotient.lift (capClass σ p) (fun _ _ h ↦ constant_on_cycles _ _ (capClass_step σ p) h)

/-- Include an old cycle in the new permutation. -/
noncomputable def includeCapCycles [Finite D] (σ : Equiv.Perm D) (p : D) :
    Cycles σ → Cycles (capPerm σ p) :=
  Quotient.map Sum.inl (fun _ _ h ↦ sameCycle_map_of_step σ (capPerm σ p) Sum.inl
    (capPerm_old_step σ p) h)

/-- Recover the new cycle from its old-cycle label or the added fixed point. -/
noncomputable def fromCapCycles [Finite D] (σ : Equiv.Perm D) (p : D) :
    Option (Cycles σ) → Cycles (capPerm σ p)
  | none => cycle (capPerm σ p) (Sum.inr false)
  | some c => includeCapCycles σ p c

/-- Cap insertion adds exactly one cycle, with an explicit bijection of cycle classes. -/
noncomputable def capCyclesEquiv [Finite D] (σ : Equiv.Perm D) (p : D) :
    Cycles (capPerm σ p) ≃ Option (Cycles σ) where
  toFun := capCycles σ p
  invFun := fromCapCycles σ p
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      rcases d with d | b
      · rfl
      · cases b
        · rfl
        · change cycle (capPerm σ p) (Sum.inl p) = cycle (capPerm σ p) (Sum.inr true)
          rw [← capPerm_true σ p, cycle_apply]
  right_inv c := by
    cases c with
    | none => rfl
    | some c =>
      induction c using Quotient.inductionOn with
      | h d => rfl

/-- The numerical cycle-count consequence, valid for any finite permutation. -/
theorem card_capCycles [Finite D] (σ : Equiv.Perm D) (p : D)
    [Fintype (Cycles σ)] [Fintype (Cycles (capPerm σ p))] :
    Fintype.card (Cycles (capPerm σ p)) = Fintype.card (Cycles σ) + 1 := by
  simpa using Fintype.card_congr (capCyclesEquiv σ p)

end SmallPresentationStatements.PermutationCycles
