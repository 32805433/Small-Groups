module

public import SmallPresentation.KunnethCommutator

/-! A central extension associated to a bilinear pairing of groups. The
construction provides a detecting group for mixed commutators in the Hopf
formula for a direct product. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable {U V T : Type} [Group U] [Group V] [AddCommGroup T]

structure BilinearExtension (β : U →* V →* Multiplicative T) where
  left : U
  right : V
  central : T

namespace BilinearExtension

variable (β : U →* V →* Multiplicative T)

def pairing (x : U) (y : V) : T := (β x y).toAdd

@[simp] theorem pairing_one_left (y : V) : pairing β 1 y = 0 := by simp [pairing]
@[simp] theorem pairing_one_right (x : U) : pairing β x 1 = 0 := by simp [pairing]
@[simp] theorem pairing_mul_left (x x' : U) (y : V) :
    pairing β (x*x') y = pairing β x y + pairing β x' y := by simp [pairing]
@[simp] theorem pairing_mul_right (x : U) (y y' : V) :
    pairing β x (y*y') = pairing β x y + pairing β x y' := by simp [pairing]
@[simp] theorem pairing_inv_left (x : U) (y : V) :
    pairing β x⁻¹ y = - pairing β x y := by simp [pairing]
@[simp] theorem pairing_inv_right (x : U) (y : V) :
    pairing β x y⁻¹ = - pairing β x y := by simp [pairing]

@[ext] theorem ext {x y : BilinearExtension β} (h₁ : x.left = y.left)
    (h₂ : x.right = y.right) (h₃ : x.central = y.central) : x = y := by
  cases x
  cases y
  simp_all

instance : Group (BilinearExtension β) where
  one := ⟨1,1,0⟩
  mul x y := ⟨x.left*y.left, x.right*y.right,
    x.central+y.central-pairing β y.left x.right⟩
  inv x := ⟨x.left⁻¹,x.right⁻¹,-x.central-pairing β x.left x.right⟩
  mul_assoc x y z := by
    apply ext
    · exact mul_assoc _ _ _
    · exact mul_assoc _ _ _
    · change x.central + y.central - pairing β y.left x.right + z.central -
          pairing β z.left (x.right*y.right) =
        x.central + (y.central + z.central - pairing β z.left y.right) -
          pairing β (y.left*z.left) x.right
      rw [pairing_mul_right, pairing_mul_left]
      abel
  one_mul x := by
    apply ext
    · exact one_mul _
    · exact one_mul _
    · change 0+x.central-pairing β x.left 1 = x.central
      simp
  mul_one x := by
    apply ext
    · exact mul_one _
    · exact mul_one _
    · change x.central+0-pairing β 1 x.right = x.central
      simp
  inv_mul_cancel x := by
    apply ext
    · exact inv_mul_cancel _
    · exact inv_mul_cancel _
    · change (-x.central-pairing β x.left x.right)+x.central-
        pairing β x.left x.right⁻¹ = 0
      rw [pairing_inv_right]
      abel

@[simp] theorem left_mul (x y : BilinearExtension β) : (x*y).left = x.left*y.left := rfl
@[simp] theorem right_mul (x y : BilinearExtension β) : (x*y).right = x.right*y.right := rfl
@[simp] theorem central_mul (x y : BilinearExtension β) :
    (x*y).central = x.central+y.central-pairing β y.left x.right := rfl
@[simp] theorem left_one : (1 : BilinearExtension β).left = 1 := rfl
@[simp] theorem right_one : (1 : BilinearExtension β).right = 1 := rfl
@[simp] theorem central_one : (1 : BilinearExtension β).central = 0 := rfl
@[simp] theorem left_inv (x : BilinearExtension β) : x⁻¹.left = x.left⁻¹ := rfl
@[simp] theorem right_inv (x : BilinearExtension β) : x⁻¹.right = x.right⁻¹ := rfl
@[simp] theorem central_inv (x : BilinearExtension β) :
    x⁻¹.central = -x.central-pairing β x.left x.right := rfl

def inl : U →* BilinearExtension β where
  toFun x := ⟨x,1,0⟩
  map_one' := rfl
  map_mul' x y := by apply ext <;> simp

def inr : V →* BilinearExtension β where
  toFun y := ⟨1,y,0⟩
  map_one' := rfl
  map_mul' x y := by apply ext <;> simp

def center : Multiplicative T →* BilinearExtension β where
  toFun t := ⟨1,1,t.toAdd⟩
  map_one' := rfl
  map_mul' x y := by apply ext <;> simp

def fst : BilinearExtension β →* U where
  toFun := left
  map_one' := rfl
  map_mul' _ _ := rfl

def snd : BilinearExtension β →* V where
  toFun := right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem inl_left (x : U) : (inl β x).left = x := rfl
@[simp] theorem inl_right (x : U) : (inl β x).right = 1 := rfl
@[simp] theorem inl_central (x : U) : (inl β x).central = 0 := rfl
@[simp] theorem inr_left (y : V) : (inr β y).left = 1 := rfl
@[simp] theorem inr_right (y : V) : (inr β y).right = y := rfl
@[simp] theorem inr_central (y : V) : (inr β y).central = 0 := rfl
@[simp] theorem center_left (t : Multiplicative T) : (center β t).left = 1 := rfl
@[simp] theorem center_right (t : Multiplicative T) : (center β t).right = 1 := rfl
@[simp] theorem center_central (t : Multiplicative T) : (center β t).central = t.toAdd := rfl

theorem center_commute (t : Multiplicative T) (x : BilinearExtension β) :
    Commute (center β t) x := by
  apply ext <;> simp [add_comm]

theorem decompose (x : BilinearExtension β) :
    inl β x.left * inr β x.right * center β (Multiplicative.ofAdd x.central) = x := by
  apply ext <;> simp

theorem commutator_inl_inr (x : U) (y : V) :
    ⁅inl β x,inr β y⁆ = center β (β x y) := by
  apply ext <;> simp [commutatorElement_def, pairing]

variable {E : Type} [Group E]

/-- The universal map into a group with the prescribed mixed commutators. -/
def lift (l : U →* E) (r : V →* E) (c : Multiplicative T →* E)
    (hc : ∀ t z, Commute (c t) z)
    (hβ : ∀ x y, c (β x y) = ⁅l x,r y⁆) : BilinearExtension β →* E where
  toFun x := l x.left * r x.right * c (Multiplicative.ofAdd x.central)
  map_one' := by simp
  map_mul' x y := by
    let a := l x.left
    let b := r x.right
    let a' := l y.left
    let b' := r y.right
    let t := c (Multiplicative.ofAdd x.central)
    let t' := c (Multiplicative.ofAdd y.central)
    let e := (c (β y.left x.right))⁻¹
    have he (z : E) : Commute e z := (hc (β y.left x.right) z).inv_left
    have hswap : b*a' = a'*b*e := by
      calc
        b*a' = e*(a'*b) := by
          dsimp [e,a',b]
          rw [hβ]
          simp [commutatorElement_def, mul_assoc]
        _ = a'*b*e := (he _).eq
    have ht : Commute t (a'*b') := hc _ _
    change l (x.left*y.left) * r (x.right*y.right) *
      c (Multiplicative.ofAdd (x.central+y.central-pairing β y.left x.right)) =
        (a*b*t)*(a'*b'*t')
    have hcentral : c (Multiplicative.ofAdd
        (x.central+y.central-pairing β y.left x.right)) = t*t'*e := by
      rw [sub_eq_add_neg]
      change c (Multiplicative.ofAdd x.central * Multiplicative.ofAdd y.central *
        (β y.left x.right)⁻¹) = _
      simp only [map_mul, map_inv]
      rfl
    rw [map_mul, map_mul, hcentral]
    change a*a'*(b*b')*(t*t'*e) = (a*b*t)*(a'*b'*t')
    symm
    calc
      (a*b*t)*(a'*b'*t') = (a*b)*(a'*b')*(t*t') := ht.mul_mul_mul_comm _ _
      _ = a*(b*a')*b'*(t*t') := by simp only [mul_assoc]
      _ = a*(a'*b*e)*b'*(t*t') := by rw [hswap]
      _ = (a*a'*b)*b'*(e*(t*t')) := by
        rw [show a*(a'*b*e) = (a*a'*b)*e by simp only [mul_assoc], (he b').right_comm]
        simp only [mul_assoc]
      _ = a*a'*(b*b')*(t*t'*e) := by rw [(he (t*t')).eq]; simp only [mul_assoc]

@[simp] theorem lift_inl (l : U →* E) (r : V →* E) (c : Multiplicative T →* E)
    (hc : ∀ t z, Commute (c t) z) (hβ : ∀ x y, c (β x y) = ⁅l x,r y⁆) (x : U) :
    lift β l r c hc hβ (inl β x) = l x := by simp [lift]

@[simp] theorem lift_inr (l : U →* E) (r : V →* E) (c : Multiplicative T →* E)
    (hc : ∀ t z, Commute (c t) z) (hβ : ∀ x y, c (β x y) = ⁅l x,r y⁆) (y : V) :
    lift β l r c hc hβ (inr β y) = r y := by simp [lift]

@[simp] theorem lift_center (l : U →* E) (r : V →* E) (c : Multiplicative T →* E)
    (hc : ∀ t z, Commute (c t) z) (hβ : ∀ x y, c (β x y) = ⁅l x,r y⁆)
    (t : Multiplicative T) : lift β l r c hc hβ (center β t) = c t := by simp [lift]

end BilinearExtension

end SmallPresentationStatements.Homology
