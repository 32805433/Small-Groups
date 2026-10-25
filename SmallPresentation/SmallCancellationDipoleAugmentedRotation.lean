module

public import SmallPresentation.SmallCancellationDipoleAugmentedOrigins
public import SmallPresentation.SmallCancellationGeometryRelativeMetric

/-! Literal doubled cyclic orders on indexed signed row occurrences. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

open Fin.NatCast

variable {O I : Type} (length : I → ℕ) [∀ i, NeZero (length i)] (labels : O → I)

abbrev Darts := Σ o : O, Fin (length (labels o)) × Bool

def rotation : Equiv.Perm (Darts length labels) where
  toFun
    | ⟨o, k, false⟩ => ⟨o, k, true⟩
    | ⟨o, k, true⟩ => ⟨o, k + 1, false⟩
  invFun
    | ⟨o, k, false⟩ => ⟨o, k - 1, true⟩
    | ⟨o, k, true⟩ => ⟨o, k, false⟩
  left_inv := by rintro ⟨o, k, b⟩; cases b <;> simp
  right_inv := by rintro ⟨o, k, b⟩; cases b <;> simp

theorem rotation_two (o : O) (k : Fin (length (labels o))) (b : Bool) :
    rotation length labels (rotation length labels ⟨o, k, b⟩) = ⟨o, k + 1, b⟩ := by
  cases b <;> rfl

theorem reverse_rotation_two (o : O) (k : Fin (length (labels o))) (b : Bool) :
    (rotation length labels).symm ((rotation length labels).symm ⟨o, k, b⟩) =
      ⟨o, k - 1, b⟩ := by
  cases b <;> rfl

theorem rotation_even (o : O) (k : Fin (length (labels o))) (b : Bool) (t : ℕ) :
    (rotation length labels)^[2 * t] ⟨o, k, b⟩ = ⟨o, k + Fin.ofNat (length (labels o)) t, b⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 + 2 * t by omega, Function.iterate_add_apply, ih]
    change rotation length labels (rotation length labels ⟨o, k + Fin.ofNat (length (labels o)) t, b⟩) = _
    rw [rotation_two]
    simp only [Fin.ofNat_eq_cast, Nat.cast_succ, add_assoc]

theorem reverse_rotation_even (o : O) (k : Fin (length (labels o))) (b : Bool) (t : ℕ) :
    (rotation length labels).symm^[2 * t] ⟨o, k, b⟩ = ⟨o, k - Fin.ofNat (length (labels o)) t, b⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 + 2 * t by omega, Function.iterate_add_apply, ih]
    change (rotation length labels).symm ((rotation length labels).symm ⟨o, k - Fin.ofNat (length (labels o)) t, b⟩) = _
    rw [reverse_rotation_two]
    simp only [Fin.ofNat_eq_cast, Nat.cast_succ, sub_sub]

theorem rotation_odd_positive (o : O) (k : Fin (length (labels o))) (t : ℕ) :
    (rotation length labels)^[2 * t + 1] ⟨o, k, false⟩ = ⟨o, k + Fin.ofNat (length (labels o)) t, true⟩ := by
  rw [Function.iterate_succ_apply', rotation_even]
  rfl

theorem reverse_rotation_odd_negative (o : O) (k : Fin (length (labels o))) (t : ℕ) :
    (rotation length labels).symm^[2 * t + 1] ⟨o, k, true⟩ = ⟨o, k - Fin.ofNat (length (labels o)) t, false⟩ := by
  rw [Function.iterate_succ_apply', reverse_rotation_even]
  rfl

theorem rotation_phase (d : Darts length labels) :
    (rotation length labels d).2.2 = !d.2.2 := by
  rcases d with ⟨o, k, b⟩
  cases b <;> rfl

theorem period (o : O) (k : Fin (length (labels o))) (b : Bool) :
    Function.minimalPeriod (rotation length labels) ⟨o, k, b⟩ = 2 * length (labels o) := by
  have hpositive : 0 < 2 * length (labels o) := by have := k.pos; omega
  have hp : Function.IsPeriodicPt (rotation length labels) (2 * length (labels o)) ⟨o, k, b⟩ := by
    change (rotation length labels)^[2 * length (labels o)] ⟨o, k, b⟩ = _
    rw [rotation_even]
    simp
  have hlo := hp.minimalPeriod_pos hpositive
  have hhi := hp.minimalPeriod_le hpositive
  by_contra he
  let t := Function.minimalPeriod (rotation length labels) ⟨o, k, b⟩
  have ht : t < 2 * length (labels o) := by dsimp [t]; omega
  have hreturn : (rotation length labels)^[t] ⟨o, k, b⟩ = ⟨o, k, b⟩ :=
    Function.isPeriodicPt_minimalPeriod _ _
  rcases Nat.mod_two_eq_zero_or_one t with hpar | hpar
  · have ht' : t = 2 * (t / 2) := by omega
    rw [ht', rotation_even] at hreturn
    have hpair := eq_of_heq (Sigma.mk.inj_iff.mp hreturn).2
    have hk := congrArg Prod.fst hpair
    have hz : Fin.ofNat (length (labels o)) (t / 2) = 0 :=
      add_left_cancel (hk.trans (add_zero k).symm)
    have hv := congrArg Fin.val hz
    change (t / 2) % length (labels o) = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    dsimp [t] at *
    omega
  · have ht' : t = 2 * (t / 2) + 1 := by omega
    rw [ht', Function.iterate_succ_apply', rotation_even] at hreturn
    have hb := congrArg (fun d : Darts length labels ↦ d.2.2) hreturn
    rw [rotation_phase] at hb
    change (!b) = b at hb
    cases b <;> contradiction

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
