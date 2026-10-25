module

public import SmallPresentation.PackingConsequences

/-!
# Normalized rows and central defects

Normalization forces perfectness of the input. The central-defect calculation identifies
the explicit corrected generators used by both packing arguments.
-/
@[expose] public section

namespace SmallPresentationStatements

open Word

variable {G : Type*} [Group G]

theorem eval_commuting_pair (x y : G) (hxy : Commute x y) (w : Word 2) :
    eval ![x, y] w = x ^ exponent ![1, 0] w * y ^ exponent ![0, 1] w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    fin_cases i
    · cases s <;> simp [ih, zpow_add, mul_assoc]
    · cases s
      · simp [ih, zpow_add]
        exact (hxy.symm.inv_left.zpow_right _).left_comm _
      · simp [ih, zpow_add]
        exact (hxy.symm.zpow_right _).left_comm _

theorem eval_mul_central {n : ℕ} (f c : Fin n → G)
    (hc : ∀ i, ∀ x : G, Commute (c i) x) (w : Word n) :
    eval (fun i ↦ f i * c i) w = eval f w * eval c w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s
    · simp only [eval_cons, Bool.false_eq_true, ↓reduceIte, ih]
      rw [(hc i (f i)).symm.inv]
      exact ((hc i (eval f w)).inv_left).mul_mul_mul_comm _ _
    · simp only [eval_cons, ↓reduceIte, ih]
      exact (hc i (eval f w)).mul_mul_mul_comm _ _

theorem eval_central_defects (q₁ q₂ c₁ c₂ : G)
    (hc₁ : ∀ x : G, Commute c₁ x) (hc₂ : ∀ x : G, Commute c₂ x) (w : Word 2) :
    eval ![q₁ * c₁, q₂ * c₂] w =
      eval ![q₁, q₂] w * c₁ ^ exponent ![1, 0] w * c₂ ^ exponent ![0, 1] w := by
  have hc : ∀ i : Fin 2, ∀ x : G, Commute (![c₁, c₂] i) x := by
    intro i x
    fin_cases i
    · exact hc₁ x
    · exact hc₂ x
  have hf : (![q₁ * c₁, q₂ * c₂] : Fin 2 → G) =
      fun i ↦ (![q₁, q₂] : Fin 2 → G) i * (![c₁, c₂] : Fin 2 → G) i := by
    funext i
    fin_cases i <;> rfl
  rw [hf, eval_mul_central _ _ hc, eval_commuting_pair c₁ c₂ (hc₁ c₂), mul_assoc]

theorem Normalized.central_defect_row {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q)
    (q₁ q₂ c₁ c₂ : G) (hc₁ : ∀ x : G, Commute c₁ x) (hc₂ : ∀ x : G, Commute c₂ x)
    (hq : ∀ i, eval ![q₁, q₂] (Q.relator i) = 1) (i : Fin L) :
    eval ![q₁ * c₁, q₂ * c₂] (Q.relator i) =
      (if i.val = 0 then c₁ else 1) * (if i.val = 1 then c₂ else 1) := by
  rw [eval_central_defects q₁ q₂ c₁ c₂ hc₁ hc₂, hq, one_mul,
    (hQ.2 i).1, (hQ.2 i).2]
  split <;> split <;> simp_all

theorem Normalized.abelianization_subsingleton {L : ℕ} {Q : FP 2 L}
    (hQ : Normalized Q) : Subsingleton (Abelianization Q.Group) := by
  let f : Fin 2 → Abelianization Q.Group := fun i ↦ Abelianization.of (PresentedGroup.of i)
  have hf : (![f 0, f 1] : Fin 2 → Abelianization Q.Group) = f := by
    funext i
    fin_cases i <;> rfl
  have hrow (i : Fin L) :
      f 0 ^ exponent ![1, 0] (Q.relator i) *
        f 1 ^ exponent ![0, 1] (Q.relator i) = 1 := by
    rw [← eval_commuting_pair (f 0) (f 1) (mul_comm _ _), hf]
    rw [show eval f (Q.relator i) =
      Abelianization.of (eval (PresentedGroup.of (rels := Q.relSet)) (Q.relator i)) from
        (map_eval Abelianization.of _ _).symm, Q.eval_relator, map_one]
  have h₀ : f 0 = 1 := by
    let i : Fin L := ⟨0, lt_of_lt_of_le (by decide) hQ.1⟩
    simpa [(hQ.2 i).1, (hQ.2 i).2, i] using hrow i
  have h₁ : f 1 = 1 := by
    let i : Fin L := ⟨1, lt_of_lt_of_le (by decide) hQ.1⟩
    simpa [(hQ.2 i).1, (hQ.2 i).2, i] using hrow i
  have hgen (i : Fin 2) : f i = 1 := by
    fin_cases i
    · exact h₀
    · exact h₁
  have hall (a : Q.Group) : Abelianization.of a = 1 :=
    PresentedGroup.generated_by Q.relSet Abelianization.of.ker hgen a
  have hab (a : Abelianization Q.Group) : a = 1 := by
    exact QuotientGroup.induction_on a hall
  exact ⟨fun x y ↦ (hab x).trans (hab y).symm⟩

theorem Normalized.commutator_eq_top {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q) :
    commutator Q.Group = ⊤ := by
  apply top_unique
  intro x _
  have hx : Abelianization.of x = 1 := hQ.abelianization_subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff x).mp hx

theorem Normalized.corrected_generators {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q)
    (q₁ q₂ c₁ c₂ : G) (hc₁ : ∀ x : G, Commute c₁ x) (hc₂ : ∀ x : G, Commute c₂ x)
    (hq : ∀ i, eval ![q₁, q₂] (Q.relator i) = 1) :
    (q₁ * c₁) *
        (eval ![q₁ * c₁, q₂ * c₂]
          (Q.relator ⟨0, lt_of_lt_of_le (by decide) hQ.1⟩))⁻¹ = q₁ ∧
      (q₂ * c₂) *
        (eval ![q₁ * c₁, q₂ * c₂]
          (Q.relator ⟨1, lt_of_lt_of_le (by decide) hQ.1⟩))⁻¹ = q₂ := by
  simp [hQ.central_defect_row q₁ q₂ c₁ c₂ hc₁ hc₂ hq]

end SmallPresentationStatements
