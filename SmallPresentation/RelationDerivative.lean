module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic.Abel

/-! The crossed derivative of a free presentation, in the free abelian group on
labelled Cayley edges. Its restriction to the presentation kernel factors through
abelianization. No small-cancellation or geometric hypotheses occur here. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

variable {X H : Type} [Group H]

abbrev Chains (H X : Type) := FreeAbelianGroup (H × X)
abbrev Vertices (H : Type) := FreeAbelianGroup H

/-- Left translation of the initial vertex of every labelled edge. -/
def shift (h : H) : Chains H X →+ Chains H X :=
  FreeAbelianGroup.map (fun e ↦ (h * e.1, e.2))

@[simp] theorem shift_of (h g : H) (x : X) :
    shift h (FreeAbelianGroup.of (g, x)) = FreeAbelianGroup.of (h * g, x) := rfl

@[simp] theorem shift_one (c : Chains H X) : shift 1 c = c := by
  have h : shift (X := X) (1 : H) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨g, x⟩
    simp
  exact DFunLike.congr_fun h c

@[simp] theorem shift_mul (h g : H) (c : Chains H X) :
    shift (h * g) c = shift h (shift g c) := by
  have he : shift (X := X) (h * g) = (shift h).comp (shift g) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨k, x⟩
    simp [mul_assoc]
  exact DFunLike.congr_fun he c

/-- The translation action, packaged for a semidirect product. -/
def shiftAction : H →* MulAut (Multiplicative (Chains H X)) where
  toFun h :=
    { toFun := fun c ↦ Multiplicative.ofAdd (shift h c.toAdd)
      invFun := fun c ↦ Multiplicative.ofAdd (shift h⁻¹ c.toAdd)
      left_inv := fun c ↦ by simp [← shift_mul]
      right_inv := fun c ↦ by simp [← shift_mul]
      map_mul' := fun c d ↦ by change shift h (c.toAdd + d.toAdd) = _; exact map_add _ _ _ }
  map_one' := by ext c; exact shift_one c.toAdd
  map_mul' h g := by ext c; exact shift_mul h g c.toAdd

variable (p : FreeGroup X →* H)

/-- Lift each generator to its initial edge and its image in the presented group. -/
def affineLift : FreeGroup X →* Multiplicative (Chains H X) ⋊[shiftAction] H :=
  FreeGroup.lift (fun x ↦ ⟨Multiplicative.ofAdd (FreeAbelianGroup.of (1, x)),
    p (FreeGroup.of x)⟩)

@[simp] theorem affineLift_right (w : FreeGroup X) : (affineLift p w).right = p w := by
  have he : SemidirectProduct.rightHom.comp (affineLift p) = p := by
    apply FreeGroup.ext_hom
    intro x
    simp [affineLift]
  exact DFunLike.congr_fun he w

/-- The signed edge chain traversed by a word starting at the identity. -/
def derivative (w : FreeGroup X) : Chains H X := (affineLift p w).left.toAdd

@[simp] theorem derivative_one : derivative p 1 = 0 := by simp [derivative]

@[simp] theorem derivative_of (x : X) :
    derivative p (FreeGroup.of x) = FreeAbelianGroup.of (1, x) := rfl

theorem derivative_mul (u v : FreeGroup X) :
    derivative p (u * v) = derivative p u + shift (p u) (derivative p v) := by
  simp only [derivative, map_mul, SemidirectProduct.mul_left, affineLift_right]
  rfl

theorem derivative_inv (w : FreeGroup X) :
    derivative p w⁻¹ = -shift (p w)⁻¹ (derivative p w) := by
  unfold derivative
  rw [map_inv]
  change shift ((affineLift p w).right)⁻¹ (-((affineLift p w).left.toAdd)) = _
  rw [affineLift_right, map_neg]

/-- The boundary of a labelled Cayley edge. -/
def boundary : Chains H X →+ Vertices H :=
  FreeAbelianGroup.lift (fun e ↦
    FreeAbelianGroup.of (e.1 * p (FreeGroup.of e.2)) - FreeAbelianGroup.of e.1)

@[simp] theorem boundary_of (h : H) (x : X) :
    boundary p (FreeAbelianGroup.of (h, x)) =
      FreeAbelianGroup.of (h * p (FreeGroup.of x)) - FreeAbelianGroup.of h := rfl

/-- Translation on vertex chains. -/
def vertexShift (h : H) : Vertices H →+ Vertices H :=
  FreeAbelianGroup.map (fun g ↦ h * g)

@[simp] theorem vertexShift_of (h g : H) :
    vertexShift h (FreeAbelianGroup.of g) = FreeAbelianGroup.of (h * g) := rfl

theorem boundary_shift (h : H) (c : Chains H X) :
    boundary p (shift h c) = vertexShift h (boundary p c) := by
  have he : (boundary p).comp (shift h) = (vertexShift h).comp (boundary p) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨g, x⟩
    simp [mul_assoc]
  exact DFunLike.congr_fun he c

theorem boundary_derivative (w : FreeGroup X) :
    boundary p (derivative p w) = FreeAbelianGroup.of (p w) - FreeAbelianGroup.of 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of x => simp
  | inv_of x ih =>
    rw [derivative_inv, map_neg, boundary_shift, ih]
    simp [vertexShift]
  | mul u v hu hv =>
    rw [derivative_mul, map_add, boundary_shift, hu, hv]
    simp only [map_sub, vertexShift_of, mul_one, map_mul]
    abel

/-- The derivative is a homomorphism when restricted to the relation subgroup. -/
def kernelDerivative : p.ker →* Multiplicative (Chains H X) where
  toFun w := Multiplicative.ofAdd (derivative p w.val)
  map_one' := derivative_one p
  map_mul' u v := by
    change derivative p (u.val * v.val) = derivative p u.val + derivative p v.val
    rw [derivative_mul, show p u.val = 1 from u.property, shift_one]

/-- The canonical derivative on the abelianized relation subgroup. -/
def relationDerivative : Additive (Abelianization p.ker) →+ Chains H X :=
  (Abelianization.lift (kernelDerivative p)).toAdditiveLeft

@[simp] theorem relationDerivative_of (w : p.ker) :
    relationDerivative p (Additive.ofMul (Abelianization.of w)) = derivative p w.val := rfl

theorem boundary_relationDerivative (c : Additive (Abelianization p.ker)) :
    boundary p (relationDerivative p c) = 0 := by
  induction c using QuotientGroup.induction_on with
  | H w =>
    change boundary p (derivative p w.val) = 0
    rw [boundary_derivative, show p w.val = 1 from w.property, sub_self]

end SmallPresentationStatements.RelationDerivative
