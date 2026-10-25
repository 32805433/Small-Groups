module

public import SmallPresentation.CyclicModuleRelationTransport

/-! Finite-period complexes for actual quotient actions on relation abelianizations. -/
@[expose] public section

namespace SmallPresentationStatements.RelationAbelianization

variable {X : Type} (N : Subgroup (FreeGroup X)) [N.Normal]

theorem quotientAction_pow (q : FreeGroup X ⧸ N) (n : ℕ) :
    CyclicModule.quotientRelationAction N q ^ n = CyclicModule.quotientRelationAction N (q ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    change (1 : AddMonoid.End _) = quotientAction N 1
    rw [quotientAction_one]
    rfl
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    exact (quotientAction_mul N (q ^ n) q).symm

theorem quotientAction_period (q : FreeGroup X ⧸ N) (n : ℕ) (h : q ^ n = 1) :
    CyclicModule.quotientRelationAction N q ^ n = 1 := by
  rw [quotientAction_pow, h]
  change quotientAction N 1 = _
  rw [quotientAction_one]
  rfl

/-- The norm/difference complex of an actual finite-period quotient conjugation action. -/
noncomputable def periodic (q : FreeGroup X ⧸ N) (n : ℕ) (h : q ^ n = 1) :
    CyclicModule.Periodic (Module N) :=
  CyclicModule.ofFiniteOrder (CyclicModule.quotientRelationAction N q) n
    (quotientAction_period N q n h)

end SmallPresentationStatements.RelationAbelianization
