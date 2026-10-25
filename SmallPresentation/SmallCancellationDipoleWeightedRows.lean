module

public import SmallPresentation.SmallCancellationDipoleBookkeeping

/-!
# Weighted conservation for repeated based-ribbon dipole deletion

Labels and signs are retained as functions on the actual finite occurrence type. The local
anchor equation proves equality of the two quotient basepoints, so equal labels and opposite
signs suffice to prove additive cancellation. Restricting these same functions to the surviving
indices allows this theorem to be used after every further geometric deletion.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon

open RelationCoordinates

variable {O X Q I J : Type} [Group Q] {words : O → List (SignedLetter X)}
    {q : FreeGroup X →* Q} (P : BasedRowRibbon words q)

/-- The selected signed weight at a marked row basepoint. -/
def rowWeight (labels : O → I) (signs : O → Bool) (select : I → Option J) (o : O) :
    Weighted.Coordinates (Q := Q) (J := J) :=
  Peiffer.weight (MonoidHom.id Q) select ((P.base o, labels o), signs o)

namespace Dipole

variable {P} (D : P.Dipole) (labels : O → I) (signs : O → Bool) (select : I → Option J)

/-- The actual geometric anchor proves cancellation of equally labelled opposite signed rows. -/
theorem rowWeight_cancel (hlabel : labels D.first = labels D.second)
    (hsign : signs D.second = !signs D.first) :
    P.rowWeight labels signs select D.first + P.rowWeight labels signs select D.second = 0 := by
  simp only [rowWeight, Peiffer.weight, MonoidHom.id_apply, ← hlabel, hsign, ← D.base_eq]
  cases signs D.first <;> simp

variable [Fintype O]

/-- The concrete deletion preserves the weighted sum with all surviving metadata restricted. -/
theorem delete_rowWeights [Fintype D.Remaining]
    (hlabel : labels D.first = labels D.second) (hsign : signs D.second = !signs D.first) :
    (∑ o, P.rowWeight labels signs select o) =
      ∑ o : D.Remaining, D.delete.rowWeight (fun r ↦ labels r.val)
        (fun r ↦ signs r.val) select o := by
  exact RowDeletion.sum_preserved D.first D.second D.distinct
    (P.rowWeight labels signs select) (D.rowWeight_cancel labels signs select hlabel hsign)

end Dipole
end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon
