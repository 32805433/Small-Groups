module

public import SmallPresentation.RelationDerivativeExact

/-! Equivariance of the presentation derivative and the quotient-group action on
the abelianized relation subgroup. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

variable {X H : Type} [Group H] (p : FreeGroup X →* H)

/-- Ambient conjugation preserves the kernel of a presentation. -/
def kernelConjugation (w : FreeGroup X) : p.ker →* p.ker where
  toFun k := ⟨w * k.val * w⁻¹, by
    change p (w * k.val * w⁻¹) = 1
    simp [show p k.val = 1 from k.property]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' k l := Subtype.ext (by simp [mul_assoc])

/-- Conjugation on the abelianized presentation kernel. -/
def relationConjugation (w : FreeGroup X) :
    Additive (Abelianization p.ker) →+ Additive (Abelianization p.ker) :=
  (Abelianization.map (kernelConjugation p w)).toAdditive

@[simp] theorem relationConjugation_of (w : FreeGroup X) (k : p.ker) :
    relationConjugation p w (Additive.ofMul (Abelianization.of k)) =
      Additive.ofMul (Abelianization.of (kernelConjugation p w k)) := rfl

theorem derivative_conjugate (w : FreeGroup X) (k : p.ker) :
    derivative p (w * k.val * w⁻¹) = shift (p w) (derivative p k.val) := by
  rw [derivative_mul, derivative_mul, derivative_inv]
  simp only [map_mul, show p k.val = 1 from k.property, mul_one, map_neg,
    ← shift_mul, mul_inv_cancel, shift_one]
  abel

/-- The canonical relation derivative intertwines conjugation and translation. -/
theorem relationDerivative_conjugation (w : FreeGroup X)
    (c : Additive (Abelianization p.ker)) :
    relationDerivative p (relationConjugation p w c) = shift (p w) (relationDerivative p c) := by
  induction c using QuotientGroup.induction_on with
  | H k =>
    change derivative p (w * k.val * w⁻¹) = shift (p w) (derivative p k.val)
    exact derivative_conjugate p w k

/-- A section realizes the quotient action; the following lemmas show independence
from the representative and the group-action laws. -/
noncomputable def relationShift (hp : Function.Surjective p) (h : H) :
    Additive (Abelianization p.ker) →+ Additive (Abelianization p.ker) :=
  relationConjugation p ((sectionOfSurjective p hp).word h)

theorem relationDerivative_shift (hp : Function.Surjective p) (h : H)
    (c : Additive (Abelianization p.ker)) :
    relationDerivative p (relationShift p hp h c) = shift h (relationDerivative p c) := by
  rw [relationShift, relationDerivative_conjugation, (sectionOfSurjective p hp).evaluates]

theorem relationShift_eq_conjugation (hp : Function.Surjective p) (w : FreeGroup X) :
    relationShift p hp (p w) = relationConjugation p w := by
  apply AddMonoidHom.ext
  intro c
  apply relationDerivative_injective p hp
  rw [relationDerivative_shift, relationDerivative_conjugation]

@[simp] theorem relationShift_one (hp : Function.Surjective p)
    (c : Additive (Abelianization p.ker)) : relationShift p hp 1 c = c := by
  apply relationDerivative_injective p hp
  rw [relationDerivative_shift, shift_one]

theorem relationShift_mul (hp : Function.Surjective p) (h g : H)
    (c : Additive (Abelianization p.ker)) :
    relationShift p hp (h * g) c = relationShift p hp h (relationShift p hp g c) := by
  apply relationDerivative_injective p hp
  rw [relationDerivative_shift, relationDerivative_shift, relationDerivative_shift, shift_mul]

end SmallPresentationStatements.RelationDerivative
