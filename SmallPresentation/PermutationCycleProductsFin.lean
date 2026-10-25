module

public import SmallPresentation.PermutationCycleProducts
public import SmallPresentation.SmallCancellationGeometryRelativeFaces

/-! Exact based cycle readings of the standard finite rotation. -/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem finRotate_period (a : Fin n) : Function.minimalPeriod (finRotate n) a = n := by
  let e : {d : Fin n // (finRotate n).SameCycle a d} ≃ Fin n := {
    toFun := Subtype.val
    invFun d := ⟨d, finRotate_sameCycle a d⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr ((orbitEquiv (finRotate n) a).trans e)

/-- Starting at zero visits the finite positions in exactly their displayed order. -/
theorem cycleBoundary_finRotate_zero :
    cycleBoundary (finRotate n) 0 = List.ofFn (fun d : Fin n ↦ d) := by
  simp only [cycleBoundary, finRotate_period]
  apply congrArg List.ofFn
  funext k
  change (finRotate n)^[k.val] 0 = k
  rw [← finCycle_eq_finRotate_iterate]
  simp [finCycle_apply]

end SmallPresentationStatements.PermutationCycles
