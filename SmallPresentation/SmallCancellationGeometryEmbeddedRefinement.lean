module

public import SmallPresentation.SmallCancellationGeometryPositiveRefinement
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Replacing an embedded invariant family of permutation cycles. -/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {A D : Type*}

/-- Replace the permutation on an embedded invariant subset, keeping its complement fixed. -/
noncomputable def replaceAlong (ρ : Equiv.Perm D) (σ τ : Equiv.Perm A)
    (f : A ↪ D) : Equiv.Perm D :=
  ρ.trans (Equiv.Perm.viaEmbedding (σ.symm.trans τ) f)

@[simp] theorem replaceAlong_apply (ρ : Equiv.Perm D) (σ τ : Equiv.Perm A)
    (f : A ↪ D) (hf : ∀ a, ρ (f a) = f (σ a)) (a : A) :
    replaceAlong ρ σ τ f (f a) = f (τ a) := by
  simp only [replaceAlong, Equiv.trans_apply, hf, Equiv.Perm.viaEmbedding_apply,
    Equiv.symm_apply_apply]

theorem invariant_complement (ρ : Equiv.Perm D) (σ : Equiv.Perm A)
    (f : A ↪ D) (hf : ∀ a, ρ (f a) = f (σ a)) {d : D}
    (hd : d ∉ Set.range f) : ρ d ∉ Set.range f := by
  rintro ⟨a, ha⟩
  apply hd
  refine ⟨σ.symm a, ρ.injective ?_⟩
  rw [hf, Equiv.apply_symm_apply]
  exact ha

theorem replaceAlong_outside (ρ : Equiv.Perm D) (σ τ : Equiv.Perm A)
    (f : A ↪ D) (hf : ∀ a, ρ (f a) = f (σ a)) {d : D}
    (hd : d ∉ Set.range f) : replaceAlong ρ σ τ f d = ρ d := by
  exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _
    (invariant_complement ρ σ f hf hd)

@[simp] theorem replaceAlong_self (ρ : Equiv.Perm D) (σ : Equiv.Perm A)
    (f : A ↪ D) (hf : ∀ a, ρ (f a) = f (σ a)) : replaceAlong ρ σ σ f = ρ := by
  classical
  apply Equiv.ext
  intro d
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    rw [replaceAlong_apply _ _ _ _ hf, hf]
  · exact replaceAlong_outside _ _ _ _ hf hd

theorem replaceAlong_cut (ρ : Equiv.Perm D) (σ τ : Equiv.Perm A)
    (f : A ↪ D) (hf : ∀ a, ρ (f a) = f (σ a)) (a b : A) :
    replaceAlong ρ σ (cutAt τ a b) f = cutAt (replaceAlong ρ σ τ f) (f a) (f b) := by
  classical
  apply Equiv.ext
  intro d
  by_cases hd : d ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hd
    simp only [replaceAlong_apply _ _ _ _ hf, cutAt_apply, f.injective.map_swap]
  · rw [replaceAlong_outside _ _ _ _ hf hd, cutAt_apply,
      replaceAlong_outside _ _ _ _ hf hd]
    have hn := invariant_complement ρ σ f hf hd
    have ha : ρ d ≠ f a := fun h ↦ hn ⟨a, h.symm⟩
    have hb : ρ d ≠ f b := fun h ↦ hn ⟨b, h.symm⟩
    simp [Equiv.swap_apply_def, ha, hb]

/-- A local sequence of actual vertex splits is still such a sequence inside a larger map. -/
theorem SplitRefinement.replaceAlong [Finite A] {σ τ : Equiv.Perm A}
    (h : SplitRefinement σ τ) (ρ : Equiv.Perm D) (f : A ↪ D)
    (hf : ∀ a, ρ (f a) = f (σ a)) :
    SplitRefinement ρ (PermutationCycles.replaceAlong ρ σ τ f) := by
  induction h with
  | refl => rw [replaceAlong_self _ _ _ hf]; exact .refl _
  | @cut τ h a b hn hc ih =>
    rw [replaceAlong_cut _ _ _ _ hf]
    apply SplitRefinement.cut ih (f a) (f b) (f.injective.ne hn)
    apply sameCycle_map_of_step τ _ f ?_ hc
    intro d
    rw [← replaceAlong_apply _ _ _ _ hf]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- A permutation that agrees on one entire original cycle has exactly that same cycle. -/
theorem sameCycle_iff_of_cycle_agreement [Finite D] (σ τ : Equiv.Perm D) (d e : D)
    (hagree : ∀ x, σ.SameCycle d x → τ x = σ x) :
    τ.SameCycle d e ↔ σ.SameCycle d e := by
  have hi (n : ℕ) : (τ ^ n) d = (σ ^ n) d := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hagree _
        (Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)), pow_succ', Equiv.Perm.mul_apply]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [hi] at hn
    rw [← hn]
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hi] at hn
    rw [← hn]
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)

/-- An invariant embedded family is a union of whole actual permutation cycles. -/
theorem embedding_range_cycle_closed [Finite D] (ρ : Equiv.Perm D) (σ : Equiv.Perm A)
    (f : A ↪ D) (hf : ∀ a, ρ (f a) = f (σ a)) {d e : D}
    (hd : d ∈ Set.range f) (hde : ρ.SameCycle d e) : e ∈ Set.range f := by
  obtain ⟨a, rfl⟩ := hd
  obtain ⟨n, rfl⟩ := hde.exists_nat_pow_eq
  refine ⟨(σ ^ n) a, ?_⟩
  clear hde
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ← hf, ih,
      pow_succ', Equiv.Perm.mul_apply]

/-- Outside the replaced invariant family, every actual vertex cycle is unchanged. -/
theorem replaceAlong_sameCycle_iff_of_outside [Finite D]
    (ρ : Equiv.Perm D) (σ τ : Equiv.Perm A) (f : A ↪ D)
    (hf : ∀ a, ρ (f a) = f (σ a)) {d : D} (hd : d ∉ Set.range f) (e : D) :
    (replaceAlong ρ σ τ f).SameCycle d e ↔ ρ.SameCycle d e := by
  apply sameCycle_iff_of_cycle_agreement
  intro x hx
  apply replaceAlong_outside _ _ _ _ hf
  intro hm
  exact hd (embedding_range_cycle_closed ρ σ f hf hm hx.symm)

end SmallPresentationStatements.PermutationCycles
