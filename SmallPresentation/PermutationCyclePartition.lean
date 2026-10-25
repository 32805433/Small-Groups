module

public import SmallPresentation.PermutationCycles

/-! Exact cycle decompositions for invariant partitions of a finite permutation. -/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D E : Type*}

def sumClass (σ : Equiv.Perm D) (τ : Equiv.Perm E) : D ⊕ E → Cycles σ ⊕ Cycles τ
  | .inl d => .inl (cycle σ d)
  | .inr e => .inr (cycle τ e)

theorem sumClass_step (σ : Equiv.Perm D) (τ : Equiv.Perm E) (x : D ⊕ E) :
    sumClass σ τ (Equiv.sumCongr σ τ x) = sumClass σ τ x := by
  cases x <;> simp [sumClass]

def sumCycles [Finite D] [Finite E] (σ : Equiv.Perm D) (τ : Equiv.Perm E) :
    Cycles (Equiv.sumCongr σ τ) → Cycles σ ⊕ Cycles τ :=
  Quotient.lift (sumClass σ τ)
    (fun _ _ h ↦ constant_on_cycles _ _ (sumClass_step σ τ) h)

def includeLeftCycles [Finite D] (σ : Equiv.Perm D) (τ : Equiv.Perm E) :
    Cycles σ → Cycles (Equiv.sumCongr σ τ) :=
  Quotient.map Sum.inl (fun _ _ h ↦ sameCycle_map_of_step _ _ Sum.inl
    (fun _ ↦ Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) h)

def includeRightCycles [Finite E] (σ : Equiv.Perm D) (τ : Equiv.Perm E) :
    Cycles τ → Cycles (Equiv.sumCongr σ τ) :=
  Quotient.map Sum.inr (fun _ _ h ↦ sameCycle_map_of_step _ _ Sum.inr
    (fun _ ↦ Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) h)

/-- A disjoint union of permutations has exactly the disjoint union of their cycles. -/
def sumCyclesEquiv [Finite D] [Finite E] (σ : Equiv.Perm D) (τ : Equiv.Perm E) :
    Cycles (Equiv.sumCongr σ τ) ≃ Cycles σ ⊕ Cycles τ where
  toFun := sumCycles σ τ
  invFun := Sum.elim (includeLeftCycles σ τ) (includeRightCycles σ τ)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d => cases d <;> rfl
  right_inv c := by
    cases c with
    | inl c => induction c using Quotient.inductionOn with | h d => rfl
    | inr c => induction c using Quotient.inductionOn with | h d => rfl

variable (σ : Equiv.Perm D) (p : D → Prop) [DecidablePred p]
    (hp : ∀ d, p (σ d) ↔ p d)

/-- Restrict a permutation to the complementary invariant subset. -/
def complementPerm : Equiv.Perm {d : D // ¬p d} :=
  σ.subtypePerm (fun d ↦ not_congr (hp d))

/-- The cycle quotient splits along any invariant partition of its elements. -/
def partitionCyclesEquiv [Finite D] : Cycles σ ≃
    Cycles (σ.subtypePerm hp) ⊕ Cycles (complementPerm σ p hp) :=
  (conjugateEquiv (Equiv.sumCongr (σ.subtypePerm hp) (complementPerm σ p hp)) σ
    (Equiv.sumCompl p) (by intro x; cases x <;> rfl)).symm.trans
    (sumCyclesEquiv _ _)

/-- Cycle counts add across an invariant partition. -/
theorem card_partitionCycles [Finite D]
    [Fintype (Cycles σ)] [Fintype (Cycles (σ.subtypePerm hp))]
    [Fintype (Cycles (complementPerm σ p hp))] :
    Fintype.card (Cycles σ) = Fintype.card (Cycles (σ.subtypePerm hp)) +
      Fintype.card (Cycles (complementPerm σ p hp)) := by
  simpa using Fintype.card_congr (partitionCyclesEquiv σ p hp)

end SmallPresentationStatements.PermutationCycles
