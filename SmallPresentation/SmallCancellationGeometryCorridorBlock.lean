module

public import SmallPresentation.SmallCancellationGeometryCorridorNested
public import SmallPresentation.SmallCancellationGeometryIdentityDarts

/-!
# Actual nested conjugator blocks

The boundary of a block has an outward path, one relator row, and an inverse return path.
Its internal rotation pairs corresponding path positions and retains the exact row rotation.
The constructions below identify this literal rotation with successive outer-pair refinements.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

abbrev CorridorDart (m n : ℕ) := Fin m ⊕ (Fin n ⊕ Fin m)

def corridorPermutation (m n : ℕ) : Equiv.Perm (CorridorDart m n) where
  toFun
    | .inl i => .inr (.inr i.rev)
    | .inr (.inl j) => .inr (.inl (finRotate n j))
    | .inr (.inr k) => .inl k.rev
  invFun
    | .inl i => .inr (.inr i.rev)
    | .inr (.inl j) => .inr (.inl ((finRotate n).symm j))
    | .inr (.inr k) => .inl k.rev
  left_inv d := by
    rcases d with d | (d | d) <;>
      simp only [Fin.rev_rev, Equiv.symm_apply_apply]
  right_inv d := by
    rcases d with d | (d | d) <;>
      simp only [Fin.rev_rev, Equiv.apply_symm_apply]

def corridorCoordinates (m n : ℕ) : CorridorDart m n ≃ Fin (n + 2 * m) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem corridorCoordinates_left (m n : ℕ) (d : Fin m) :
    (corridorCoordinates m n (.inl d)).val = d.val := rfl

@[simp] theorem corridorCoordinates_row (m n : ℕ) (d : Fin n) :
    (corridorCoordinates m n (.inr (.inl d))).val = m + d.val := rfl

@[simp] theorem corridorCoordinates_right (m n : ℕ) (d : Fin m) :
    (corridorCoordinates m n (.inr (.inr d))).val = m + (n + d.val) := rfl

def corridorSucc (m n : ℕ) : Fin 2 ⊕ CorridorDart m n → CorridorDart (m + 1) n
  | .inl i => if i = 0 then .inr (.inr (Fin.last m)) else .inl 0
  | .inr (.inl i) => .inl i.succ
  | .inr (.inr (.inl j)) => .inr (.inl j)
  | .inr (.inr (.inr k)) => .inr (.inr k.castSucc)

def corridorPred (m n : ℕ) : CorridorDart (m + 1) n → Fin 2 ⊕ CorridorDart m n
  | .inl i => Fin.cases (.inl 1) (fun j ↦ .inr (.inl j)) i
  | .inr (.inl j) => .inr (.inr (.inl j))
  | .inr (.inr k) => Fin.lastCases (.inl 0) (fun j ↦ .inr (.inr (.inr j))) k

theorem corridorPred_succ (m n : ℕ) (d : Fin 2 ⊕ CorridorDart m n) :
    corridorPred m n (corridorSucc m n d) = d := by
  rcases d with i | (i | (j | k))
  · induction i using Fin.cases with
    | zero => simp [corridorSucc, corridorPred]
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [corridorSucc, corridorPred]
  · simp [corridorSucc, corridorPred]
  · rfl
  · simp [corridorSucc, corridorPred]

theorem corridorSucc_pred (m n : ℕ) (d : CorridorDart (m + 1) n) :
    corridorSucc m n (corridorPred m n d) = d := by
  rcases d with i | (j | k)
  · induction i using Fin.cases with
    | zero => simp [corridorSucc, corridorPred]
    | succ i => simp [corridorSucc, corridorPred]
  · rfl
  · induction k using Fin.lastCases with
    | last => simp [corridorSucc, corridorPred]
    | cast k => simp [corridorSucc, corridorPred]

def corridorSuccEquiv (m n : ℕ) : Fin 2 ⊕ CorridorDart m n ≃ CorridorDart (m + 1) n where
  toFun := corridorSucc m n
  invFun := corridorPred m n
  left_inv := corridorPred_succ m n
  right_inv := corridorSucc_pred m n

theorem corridorSucc_intertwines (m n : ℕ) (d : Fin 2 ⊕ CorridorDart m n) :
    corridorSuccEquiv m n (Equiv.sumCongr (finRotate 2) (corridorPermutation m n) d) =
      corridorPermutation (m + 1) n (corridorSuccEquiv m n d) := by
  rcases d with i | (i | (j | k))
  · induction i using Fin.cases with
    | zero =>
      have h : finRotate 2 0 = 1 := by decide
      change corridorSucc m n (.inl (finRotate 2 0)) = _
      rw [h]
      simp [corridorSuccEquiv, corridorSucc, corridorPermutation]
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have h : finRotate 2 1 = 0 := by decide
      change corridorSucc m n (.inl (finRotate 2 1)) = _
      rw [h]
      simp [corridorSuccEquiv, corridorSucc, corridorPermutation]
  · simp [corridorSuccEquiv, corridorSucc, corridorPermutation, Fin.rev_succ]
  · rfl
  · simp [corridorSuccEquiv, corridorSucc, corridorPermutation, Fin.rev_castSucc]

theorem wrapCoordinates_left_zero (n : ℕ) :
    (wrapCoordinates n (.inl 0)).val = n + 1 := by
  have h : wrapCoordinates n (.inl 0) = Fin.last (n + 1) := by
    apply (finRotate (n + 2)).injective
    simp only [wrapCoordinates, Equiv.trans_apply, Equiv.apply_symm_apply]
    apply Fin.ext
    change 0 = (finRotate (n + 2) (Fin.last (n + 1))).val
    rw [finRotate_last]
    rfl
  exact congrArg Fin.val h

theorem wrapCoordinates_left_one (n : ℕ) :
    (wrapCoordinates n (.inl 1)).val = 0 := by
  have h : wrapCoordinates n (.inl 1) = (0 : Fin (n + 2)) := by
    apply (finRotate (n + 2)).injective
    simp only [wrapCoordinates, Equiv.trans_apply, Equiv.apply_symm_apply]
    apply Fin.ext
    change 1 = (finRotate (n + 2) 0).val
    rw [finRotate_value]
    simp only [Fin.val_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n + 2)]
  exact congrArg Fin.val h

theorem wrapCoordinates_right (n : ℕ) (d : Fin n) :
    (wrapCoordinates n (.inr d)).val = d.val + 1 := by
  let j : Fin (n + 2) := ⟨d.val + 1, by omega⟩
  have h : wrapCoordinates n (.inr d) = j := by
    apply (finRotate (n + 2)).injective
    simp only [wrapCoordinates, Equiv.trans_apply, Equiv.apply_symm_apply]
    apply Fin.ext
    change 2 + d.val = (finRotate (n + 2) j).val
    rw [finRotate_value]
    change 2 + d.val = (d.val + 1 + 1) % (n + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  exact congrArg Fin.val h

/-- The typed outer-pair insertion has exactly the original literal linear order. -/
theorem corridorCoordinates_succ (m n : ℕ) (d : Fin 2 ⊕ CorridorDart m n) :
    corridorCoordinates (m + 1) n (corridorSuccEquiv m n d) =
      finCongr (by omega : (n + 2 * m) + 2 = n + 2 * (m + 1))
        (wrapCoordinates (n + 2 * m)
          (Equiv.sumCongr (Equiv.refl _) (corridorCoordinates m n) d)) := by
  apply Fin.ext
  change (corridorCoordinates (m + 1) n (corridorSucc m n d)).val =
    (wrapCoordinates (n + 2 * m)
      (Equiv.sumCongr (Equiv.refl _) (corridorCoordinates m n) d)).val
  rcases d with i | (i | (j | k))
  · induction i using Fin.cases with
    | zero =>
      change (m + 1) + (n + m) = (wrapCoordinates (n + 2 * m) (.inl 0)).val
      rw [wrapCoordinates_left_zero]
      omega
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change 0 = (wrapCoordinates (n + 2 * m) (.inl 1)).val
      exact (wrapCoordinates_left_one _).symm
  · change i.val + 1 = (wrapCoordinates _ (.inr (corridorCoordinates m n (.inl i)))).val
    rw [wrapCoordinates_right, corridorCoordinates_left]
  · change (m + 1) + j.val =
      (wrapCoordinates _ (.inr (corridorCoordinates m n (.inr (.inl j))))).val
    rw [wrapCoordinates_right, corridorCoordinates_row]
    omega
  · change (m + 1) + (n + k.val) =
      (wrapCoordinates _ (.inr (corridorCoordinates m n (.inr (.inr k))))).val
    rw [wrapCoordinates_right, corridorCoordinates_right]
    omega

theorem corridorPermutation_wrapped (m n : ℕ) :
    transport (corridorCoordinates (m + 1) n) (corridorPermutation (m + 1) n) =
      transport (finCongr (by omega : (n + 2 * m) + 2 = n + 2 * (m + 1)))
        (wrapPermutation (transport (corridorCoordinates m n) (corridorPermutation m n))) := by
  apply transport_eq
  intro d
  obtain ⟨x, rfl⟩ := (corridorSuccEquiv m n).surjective d
  rw [← corridorSucc_intertwines, corridorCoordinates_succ, corridorCoordinates_succ,
    transport_at]
  rw [wrapPermutation, transport_at]
  congr 2
  cases x with
  | inl i => rfl
  | inr d =>
    change Sum.inr (corridorCoordinates m n (corridorPermutation m n d)) =
      Sum.inr (transport (corridorCoordinates m n) (corridorPermutation m n)
        (corridorCoordinates m n d))
    rw [transport_at]

/-- The literal path/row/inverse-path partition is obtained from its original circle by cuts. -/
theorem corridorPermutation_refinement (m n : ℕ) :
    SplitRefinement (finRotate (n + 2 * m))
      (transport (corridorCoordinates m n) (corridorPermutation m n)) := by
  induction m with
  | zero =>
    have he : transport (corridorCoordinates 0 n) (corridorPermutation 0 n) =
        finRotate (n + 2 * 0) := by
      apply transport_eq
      intro d
      rcases d with d | (d | d)
      · exact Fin.elim0 d
      · apply Fin.ext
        change 0 + (finRotate n d).val =
          (finRotate (n + 2 * 0) (corridorCoordinates 0 n (.inr (.inl d)))).val
        simp only [finRotate_value]
        rw [corridorCoordinates_row]
        simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]
      · exact Fin.elim0 d
    rw [he]
    exact .refl _
  | succ m ih =>
    let e := finCongr (by omega : (n + 2 * m) + 2 = n + 2 * (m + 1))
    have he : transport e (finRotate ((n + 2 * m) + 2)) = finRotate (n + 2 * (m + 1)) :=
      transport_eq _ _ _ (finRotate_finCongr _)
    have hh := ih.wrap.transport e
    rw [he, ← corridorPermutation_wrapped] at hh
    exact hh

end SmallPresentationStatements.PermutationCycles
