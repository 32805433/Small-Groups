module

public import SmallPresentation.ConversionWords
public import SmallPresentation.CentralDefects

/-! # Perfectness of the literal perfectification

The determinant-one dummy rows force every homomorphism to an abelian group to
kill both displayed generators. This is a direct presentation calculation, with
no topological or small-cancellation input.
-/
@[expose] public section

namespace SmallPresentationStatements.Conversion
open Word

@[simp] theorem eval_centralSection₁_commutative {A : Type*} [CommGroup A] (x y : A) :
    eval ![x, y] centralSection₁ = x := by
  rw [eval_commuting_pair x y (mul_comm _ _) ]
  simp

@[simp] theorem eval_centralSection₂_commutative {A : Type*} [CommGroup A] (x y : A) :
    eval ![x, y] centralSection₂ = y := by
  rw [eval_commuting_pair x y (mul_comm _ _)]
  simp

theorem perfectification_commutative_generators {k μ : ℕ} (T : FP k μ)
    {A : Type*} [CommGroup A] (f : Fin 2 → A)
    (h : ∀ i, eval f ((perfectification T).relator i) = 1) : f 0 = 1 ∧ f 1 = 1 := by
  have h₁ : eval f dummy₁ = 1 := by
    simpa only [perfectification_dummy₁] using h ⟨μ, by omega⟩
  have h₂ : eval f dummy₂ = 1 := by
    simpa only [perfectification_dummy₂] using h ⟨μ + 1, by omega⟩
  have hf : (![f 0, f 1] : Fin 2 → A) = f := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rw [← eval_centralSection₁_commutative (f 0) (f 1), hf]
    simp [centralSection₁, h₁, h₂]
  · rw [← eval_centralSection₂_commutative (f 0) (f 1), hf]
    simp [centralSection₂, h₁, h₂]

/-- The literal perfectification has trivial abelianization, for every input presentation. -/
theorem perfectification_abelianization_subsingleton {k μ : ℕ} (T : FP k μ) :
    Subsingleton (Abelianization (perfectification T).Group) := by
  let Q := perfectification T
  let f : Fin 2 → Abelianization Q.Group := fun i ↦ Abelianization.of (PresentedGroup.of i)
  have hrow (i : Fin (μ + 2)) : eval f (Q.relator i) = 1 := by
    rw [show eval f (Q.relator i) =
      Abelianization.of (eval (PresentedGroup.of (rels := Q.relSet)) (Q.relator i)) from
        (map_eval Abelianization.of _ _).symm, Q.eval_relator, map_one]
  have hgen (i : Fin 2) : f i = 1 := by
    have h := perfectification_commutative_generators T f hrow
    fin_cases i
    · exact h.1
    · exact h.2
  have hall (a : Q.Group) : Abelianization.of a = 1 :=
    PresentedGroup.generated_by Q.relSet Abelianization.of.ker hgen a
  have hab (a : Abelianization Q.Group) : a = 1 :=
    QuotientGroup.induction_on a hall
  exact ⟨fun x y ↦ (hab x).trans (hab y).symm⟩

theorem perfectification_commutator_eq_top {k μ : ℕ} (T : FP k μ) :
    commutator (perfectification T).Group = ⊤ := by
  apply top_unique
  intro x _
  have hx : Abelianization.of x = 1 :=
    (perfectification_abelianization_subsingleton T).elim _ _
  exact (QuotientGroup.eq_one_iff x).mp hx

end SmallPresentationStatements.Conversion
