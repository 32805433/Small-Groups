module

public import SmallPresentation.SmallCancellationData
public import SmallPresentation.SmallCancellationDipolePairRefinement

/-!
# Exact origin coordinates of signed augmented occurrences

A negative relator occurrence uses the literal reversed syllable order. Its forward
reading therefore starts at position `k + 1` in the API's negated-position convention.
Reading a trailing negative marker backwards reverses the direction and negates that
position. Equality of these actual indexed origins forces equal labels, opposite signs,
and literal complementary original syllable positions.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {I : Type} (length : I → ℕ) [∀ i, NeZero (length i)]

/-- Origin of the positive marker at a literal position in a signed row occurrence. -/
def positiveOrigin (i : I) (sign : Bool) (k : Fin (length i)) : Origin length :=
  ⟨i, sign, bif sign then k else k + 1⟩

/-- Origin read backwards from the negative marker of that same original syllable. -/
def negativeOrigin (i : I) (sign : Bool) (k : Fin (length i)) : Origin length :=
  ⟨i, !sign, -(positiveOrigin length i sign k).position⟩

theorem rev_eq_neg_succ {n : ℕ} [NeZero n] (k : Fin n) : k.rev = -(k + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k.pos.ne'
  have hl : Fin.last m = (-1 : Fin (m + 1)) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.coe_neg_one]
  rw [← Fin.last_sub, hl]
  abel

/-- Matched positive/backwards-negative origins determine the exact inverse-row incidence data. -/
theorem matched_origin_data (i j : I) (ε δ : Bool)
    (k : Fin (length i)) (l : Fin (length j))
    (h : positiveOrigin length i ε k = negativeOrigin length j δ l) :
    i = j ∧ δ = !ε ∧ k.val + l.val + 1 = length i := by
  have hij : i = j := congrArg Origin.row h
  subst j
  have hs : ε = !δ := congrArg Origin.forward h
  have hp : (bif ε then k else k + 1) = -(bif δ then l else l + 1) := by
    have hh := congrArg (fun a : Origin length ↦ (⟨a.row, a.position⟩ : Σ i, Fin (length i))) h
    exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  have hδ : δ = !ε := by
    simpa only [Bool.not_not] using (congrArg Bool.not hs).symm
  have hk : k = l.rev := by
    rw [rev_eq_neg_succ]
    cases ε <;> cases δ
    · cases hs
    · change k + 1 = -l at hp
      exact (eq_sub_iff_add_eq.mpr hp).trans (by abel)
    · exact hp
    · cases hs
  have hv := congrArg Fin.val hk
  simp only [Fin.val_rev] at hv
  exact ⟨rfl, hδ, by have := l.isLt; omega⟩

/-- The metric matched-origin conclusion gives exactly the indexed marker dipole data. -/
theorem matched_occurrences {O : Type} (labels : O → I) (signs : O → Bool)
    (first second : O) (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (h : positiveOrigin length (labels first) (signs first) k =
      negativeOrigin length (labels second) (signs second) l) :
    first ≠ second ∧ labels first = labels second ∧ signs second = !signs first ∧
      2 * k.val + (2 * l.val + 1) + 1 = 2 * length (labels first) := by
  obtain ⟨hlabel, hsign, hpos⟩ := matched_origin_data length _ _ _ _ k l h
  refine ⟨?_, hlabel, hsign, by omega⟩
  intro he
  subst second
  cases hs : signs first <;> simp only [hs, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false] at hsign

variable {A : Type} (G : A → Type) [∀ a, Group (G a)]
    (rows : ∀ i, Fin (length i) → Syllable G)

/-- A signed occurrence uses the original row or its literal reversed inverse sequence. -/
def literalSyllable (i : I) (sign : Bool) (k : Fin (length i)) : Syllable G :=
  bif sign then rows i k else inverseSyllable G (rows i k.rev)

/-- All forward syllables at a positive marker have the claimed original cyclic coordinates. -/
theorem positive_syllableAt (i : I) (sign : Bool) (k : Fin (length i)) (t : ℕ) :
    syllableAt G length rows (positiveOrigin length i sign k) t =
      literalSyllable length G rows i sign (k + Fin.ofNat (length i) t) := by
  cases sign with
  | true => rfl
  | false =>
    change inverseSyllable G (rows i (-((k + 1) + Fin.ofNat (length i) t))) =
      inverseSyllable G (rows i (k + Fin.ofNat (length i) t).rev)
    rw [rev_eq_neg_succ]
    congr 2
    abel

/-- Reading backwards from a negative marker reverses and inverts the entire literal row. -/
theorem negative_syllableAt (i : I) (sign : Bool) (k : Fin (length i)) (t : ℕ) :
    syllableAt G length rows (negativeOrigin length i sign k) t =
      inverseSyllable G (literalSyllable length G rows i sign (k - Fin.ofNat (length i) t)) := by
  cases sign with
  | true =>
    change inverseSyllable G (rows i (-(-k + Fin.ofNat (length i) t))) =
      inverseSyllable G (rows i (k - Fin.ofNat (length i) t))
    congr 2
    abel
  | false =>
    change rows i (-(k + 1) + Fin.ofNat (length i) t) =
      inverseSyllable G (inverseSyllable G (rows i (k - Fin.ofNat (length i) t).rev))
    have hinv (s : Syllable G) : inverseSyllable G (inverseSyllable G s) = s := by
      rcases s with ⟨a, x⟩
      exact congrArg (Sigma.mk a) (inv_inv x)
    rw [hinv, rev_eq_neg_succ]
    congr 1
    abel

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
