module

public import SmallPresentation.SmallCancellationData
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Augmenting a presentation over a free product

The augmentation replaces a syllable `g ∈ G a` by `x a * g * (x a)⁻¹` in the free
product with auxiliary letters. The resulting substitution is an automorphism, with inverse
conjugating each factor by the inverse auxiliary letter. These constructions are independent of
small cancellation and place no finiteness or nontriviality assumptions on the factors.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Augmentation

variable {A : Type} (G : A → Type) [∀ a, Group (G a)]

/-- The original indexed free product. -/
abbrev Base := Monoid.CoprodI G

/-- The free product after adjoining one auxiliary letter for each factor. -/
abbrev Ambient := Monoid.Coprod (Base G) (FreeGroup A)

/-- The original free product, before any relations have been imposed. -/
def base : Base G →* Ambient G := Monoid.Coprod.inl

/-- Inclusion of the free auxiliary group. -/
def letters : FreeGroup A →* Ambient G := Monoid.Coprod.inr

/-- The auxiliary generator associated to a factor. -/
def letter (a : A) : Ambient G := letters G (FreeGroup.of a)

/-- An original factor in the augmented ambient group. -/
def factor (a : A) : G a →* Ambient G := (base G).comp Monoid.CoprodI.of

/-- Factorwise conjugation by the auxiliary generators, with a choice of direction. -/
def conjugatedFactor (inverse : Bool) (a : A) : G a →* Ambient G :=
  (MulAut.conj (if inverse then (letter G a)⁻¹ else letter G a)).toMonoidHom.comp
    (factor G a)

@[simp] theorem conjugatedFactor_apply (inverse : Bool) (a : A) (g : G a) :
    conjugatedFactor G inverse a g =
      (if inverse then (letter G a)⁻¹ else letter G a) * factor G a g *
        (if inverse then (letter G a)⁻¹ else letter G a)⁻¹ := rfl

/-- Extend the conjugations to the original free product. -/
def conjugatedBase (inverse : Bool) : Base G →* Ambient G :=
  Monoid.CoprodI.lift (conjugatedFactor G inverse)

@[simp] theorem conjugatedBase_of (inverse : Bool) (a : A) (g : G a) :
    conjugatedBase G inverse (Monoid.CoprodI.of g) = conjugatedFactor G inverse a g :=
  Monoid.CoprodI.lift_of _ _

/-- The substitution fixes the auxiliary group and conjugates every original factor. -/
def substitution (inverse : Bool) : Ambient G →* Ambient G :=
  Monoid.Coprod.lift (conjugatedBase G inverse) (letters G)

@[simp] theorem substitution_base (inverse : Bool) (g : Base G) :
    substitution G inverse (base G g) = conjugatedBase G inverse g := by
  simp [substitution, base]

@[simp] theorem substitution_letters (inverse : Bool) (w : FreeGroup A) :
    substitution G inverse (letters G w) = letters G w := by
  simp [substitution, letters]

@[simp] theorem substitution_letter (inverse : Bool) (a : A) :
    substitution G inverse (letter G a) = letter G a :=
  substitution_letters G inverse _

@[simp] theorem substitution_factor (inverse : Bool) (a : A) (g : G a) :
    substitution G inverse (factor G a g) = conjugatedFactor G inverse a g := by
  change substitution G inverse (base G (Monoid.CoprodI.of g)) = _
  rw [substitution_base, conjugatedBase_of]

/-- Substitution in one direction followed by the other is the identity. -/
theorem substitution_comp (inverse : Bool) :
    (substitution G (!inverse)).comp (substitution G inverse) = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro a
    ext g
    change substitution G (!inverse) (substitution G inverse (factor G a g)) =
      factor G a g
    cases inverse <;> simp [conjugatedFactor_apply, mul_assoc]
  · apply MonoidHom.ext
    intro w
    change substitution G (!inverse) (substitution G inverse (letters G w)) = letters G w
    simp

/-- The general augmentation automorphism. -/
def equiv : Ambient G ≃* Ambient G :=
  (substitution G false).toMulEquiv (substitution G true)
    (substitution_comp G false) (substitution_comp G true)

@[simp] theorem equiv_base (g : Base G) :
    equiv G (base G g) = conjugatedBase G false g := substitution_base G false g

@[simp] theorem equiv_factor (a : A) (g : G a) :
    equiv G (factor G a g) = letter G a * factor G a g * (letter G a)⁻¹ := by
  exact substitution_factor G false a g

@[simp] theorem equiv_letters (w : FreeGroup A) : equiv G (letters G w) = letters G w :=
  substitution_letters G false w

@[simp] theorem equiv_symm_factor (a : A) (g : G a) :
    (equiv G).symm (factor G a g) = (letter G a)⁻¹ * factor G a g * letter G a := by
  change substitution G true (factor G a g) = _
  rw [substitution_factor]
  simp only [conjugatedFactor_apply, ite_true, inv_inv]

@[simp] theorem equiv_symm_letters (w : FreeGroup A) :
    (equiv G).symm (letters G w) = letters G w := substitution_letters G true w

/-- The augmented relator associated to an arbitrary word in the original free product. -/
def augment (r : Base G) : Ambient G := equiv G (base G r)

@[simp] theorem augment_factor (a : A) (g : G a) :
    augment G (Monoid.CoprodI.of g) = letter G a * factor G a g * (letter G a)⁻¹ :=
  equiv_factor G a g

@[simp] theorem augment_mul (r s : Base G) : augment G (r * s) = augment G r * augment G s :=
  (conjugatedBase G false).map_mul r s

end SmallPresentationStatements.RelativeSmallCancellation.Augmentation
