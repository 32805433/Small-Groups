module

public import SmallPresentation.SmallCancellationGeometryCorridorRefinement

/-!
# Noncrossing sums and nested corridor pairs are actual vertex refinements

These operations are exactly the two patterns in a concatenated identity boundary:
separating consecutive occurrence blocks, and pairing the two outermost sides of
one conjugator corridor. Both are proved to be finite sequences of genuine cuts.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D E B : Type*}

theorem transport_eq (e : D ≃ E) (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (h : ∀ d, e (σ d) = τ (e d)) : transport e σ = τ := by
  apply Equiv.ext
  intro x
  obtain ⟨d, rfl⟩ := e.surjective x
  rw [transport_at]
  exact h d

theorem transport_trans (e : D ≃ E) (f : E ≃ B) (σ : Equiv.Perm D) :
    transport f (transport e σ) = transport (e.trans f) σ := by
  apply Equiv.ext
  intro x
  rfl

theorem finRotate_value {N : ℕ} (d : Fin N) :
    (finRotate N d).val = (d.val + 1) % N := by
  rw [finRotate_apply]
  change (d.val + (1 % N)) % N = _
  exact Nat.add_mod_mod _ _ _

/-- Splitting a circular boundary into two consecutive blocks is a genuine vertex cut.
Empty blocks are handled as identity relabellings, rather than as extra vertices. -/
theorem split_rotation_sum (m n : ℕ) :
    SplitRefinement (finRotate (m + n))
      (transport finSumFinEquiv (Equiv.sumCongr (finRotate m) (finRotate n))) := by
  cases m with
  | zero =>
    have he : transport finSumFinEquiv (Equiv.sumCongr (finRotate 0) (finRotate n)) =
        finRotate (0 + n) := by
      apply transport_eq
      intro d
      cases d with
      | inl d => exact Fin.elim0 d
      | inr d =>
        apply Fin.ext
        change 0 + (finRotate n d).val =
          (finRotate (0 + n) (finSumFinEquiv (Sum.inr d))).val
        simp only [finRotate_value, Nat.zero_add]
        simp
    rw [he]
    exact .refl _
  | succ m =>
    cases n with
    | zero =>
      have he : transport finSumFinEquiv (Equiv.sumCongr (finRotate (m + 1)) (finRotate 0)) =
          finRotate ((m + 1) + 0) := by
        apply transport_eq
        intro d
        cases d with
        | inl d =>
          apply Fin.ext
          change (finRotate (m + 1) d).val =
            (finRotate ((m + 1) + 0) (finSumFinEquiv (Sum.inl d))).val
          simp only [finRotate_value, Nat.add_zero]
          rfl
        | inr d => exact Fin.elim0 d
      rw [he]
      exact .refl _
    | succ n =>
      have he : transport finSumFinEquiv
          (Equiv.sumCongr (finRotate (m + 1)) (finRotate (n + 1))) = intervalSplit m n :=
        transport_eq _ _ _ (intervalSplit_intertwines m n)
      rw [he]
      have hs : intervalSplit m n = cutAt (finRotate _)
          (intervalStartLeft m n) (intervalStartRight m n) := by
        classical
        ext d
        simp only [intervalSplit, cutAt_apply, Equiv.trans_apply, Equiv.swap_apply_def]
        split_ifs <;> rfl
      rw [hs]
      change SplitRefinement (finRotate _) (cutAt (finRotate _)
        (intervalStartLeft m n) (intervalStartRight m n))
      apply SplitRefinement.single
      · intro h
        have hh := congrArg Fin.val h
        change 0 = m + 1 at hh
        omega
      · exact finRotate_sameCycle _ _

/-- Independently refining two consecutive blocks gives an actual refinement of their circle. -/
theorem SplitRefinement.append {m n : ℕ} {σ : Equiv.Perm (Fin m)} {τ : Equiv.Perm (Fin n)}
    (hσ : SplitRefinement (finRotate m) σ) (hτ : SplitRefinement (finRotate n) τ) :
    SplitRefinement (finRotate (m + n))
      (PermutationCycles.transport finSumFinEquiv (Equiv.sumCongr σ τ)) :=
  (split_rotation_sum m n).trans
    (((hσ.sum_left (finRotate n)).trans (hτ.sum_right σ)).transport finSumFinEquiv)

/-- Place the two ends of a new corridor outside the whole previous boundary. -/
def wrapCoordinates (n : ℕ) : Fin 2 ⊕ Fin n ≃ Fin (n + 2) :=
  finSumFinEquiv.trans ((finCongr (Nat.add_comm 2 n)).trans (finRotate (n + 2)).symm)

def wrapPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 2)) :=
  transport (wrapCoordinates n) (Equiv.sumCongr (finRotate 2) σ)

/-- Adding a pair outside a noncrossing vertex refinement remains a genuine refinement. -/
theorem SplitRefinement.wrap {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : SplitRefinement (finRotate n) σ) :
    SplitRefinement (finRotate (n + 2)) (wrapPermutation σ) := by
  let e := (finCongr (Nat.add_comm 2 n)).trans (finRotate (n + 2)).symm
  have he : PermutationCycles.transport e (finRotate (2 + n)) = finRotate (n + 2) := by
    apply transport_eq
    intro d
    simp only [e, Equiv.trans_apply, finRotate_finCongr, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
  have hh := (SplitRefinement.append (.refl (finRotate 2)) h).transport e
  rw [he, transport_trans] at hh
  exact hh

end SmallPresentationStatements.PermutationCycles
