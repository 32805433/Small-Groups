module

public import SmallPresentation.HostModel

/-! Explicit coordinates on each residue fiber modulo `p²`: the second
coordinate is the quotient of the least nonnegative representative by `p`. -/
@[expose] public section

namespace SmallPresentationStatements.Host

variable (p : ℕ) [NeZero p]

theorem fiber_encode_lt (c : ZMod p) (i : Fin p) : c.val + p * i.val < p ^ 2 := by
  calc
    c.val + p * i.val < p + p * i.val := Nat.add_lt_add_right (ZMod.val_lt c) _
    _ = p * (i.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ p * p := Nat.mul_le_mul_left p i.isLt
    _ = p ^ 2 := (pow_two p).symm

theorem fiber_quot_lt (v : ZMod (p ^ 2)) : v.val / p < p :=
  (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne p))).mpr
    (by simpa only [pow_two] using ZMod.val_lt v)

def fiberEquiv (c : ZMod p) : {v : ZMod (p ^ 2) // residue p v = c} ≃ Fin p where
  toFun v := ⟨v.1.val / p, fiber_quot_lt p v.1⟩
  invFun i := ⟨((c.val + p * i.val : ℕ) : ZMod (p ^ 2)), by
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]⟩
  left_inv v := by
    apply Subtype.ext
    apply ZMod.val_injective
    change (((c.val + p * (v.1.val / p) : ℕ) : ZMod (p ^ 2))).val = v.1.val
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (fiber_encode_lt p c ⟨v.1.val / p, fiber_quot_lt p v.1⟩)]
    have hmod : v.1.val % p = c.val := by
      have h := congrArg ZMod.val v.property
      simpa only [residue, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] using h
    rw [← hmod]
    exact Nat.mod_add_div _ _
  right_inv i := by
    apply Fin.ext
    change (((c.val + p * i.val : ℕ) : ZMod (p ^ 2))).val / p = i.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (fiber_encode_lt p c i),
      Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne p)),
      Nat.div_eq_of_lt (ZMod.val_lt c), Nat.zero_add]

end SmallPresentationStatements.Host
