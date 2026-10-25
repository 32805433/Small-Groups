module

public import SmallPresentation.SmallCancellationDipolePlanarity
public import SmallPresentation.SmallCancellationDipoleWeightedRows

/-!
# Actual finite dipole reduction preserving all quotient weights

Repeated concrete full-row deletion terminates because each step removes two original
occurrence indices. The result retains the original row words and quotient basepoints,
is spherical, has the same selected weighted sum, and contains no equally labelled
opposite signed anchored dipole. No dipole-existence or reduction theorem is assumed.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon

variable {X Q I J : Type} [Group Q] (q : FreeGroup X →* Q) (select : I → Option J)

/-- No actual anchored inverse-row pair has equal indexed labels and opposite signs. -/
def NoMatchedDipole {q : FreeGroup X →* Q} {O : Type} {words : O → List (SignedLetter X)}
    (P : BasedRowRibbon words q) (labels : O → I) (signs : O → Bool) : Prop :=
  ∀ D : P.Dipole, labels D.first = labels D.second → signs D.second ≠ !signs D.first

private theorem exists_reduced_aux (n : ℕ) :
    ∀ (O : Type) (_ : Fintype O) (words : O → List (SignedLetter X))
      (P : BasedRowRibbon words q) (labels : O → I) (signs : O → Bool),
      Fintype.card O = n → P.map.EulerEquality →
      ∃ (R : Type) (_ : Fintype R) (retain : R ↪ O)
        (T : BasedRowRibbon (fun r ↦ words (retain r)) q),
        (∀ r, T.base r = P.base (retain r)) ∧ T.map.EulerEquality ∧
        T.NoMatchedDipole (fun r ↦ labels (retain r)) (fun r ↦ signs (retain r)) ∧
        (∑ o, P.rowWeight labels signs select o) =
          ∑ r, T.rowWeight (fun r ↦ labels (retain r)) (fun r ↦ signs (retain r)) select r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro O inst words P labels signs hn hEuler
    classical
    by_cases hred : P.NoMatchedDipole labels signs
    · exact ⟨O, inst, Function.Embedding.refl O, P, fun _ ↦ rfl, hEuler, hred, rfl⟩
    · simp only [NoMatchedDipole] at hred
      push Not at hred
      obtain ⟨D, hlabel, hsign⟩ := hred
      have hlt : Fintype.card D.Remaining < n := by
        rw [← hn]
        exact RowDeletion.card_remaining_lt D.first D.second D.distinct
      obtain ⟨R, instR, retain, T, hbase, hE, hR, hw⟩ :=
        ih _ hlt D.Remaining inferInstance D.RemainingWords D.delete
          (fun o ↦ labels o.val) (fun o ↦ signs o.val) rfl (D.delete_euler hEuler)
      let : Fintype R := instR
      let retain' : R ↪ O := retain.trans ⟨Subtype.val, Subtype.val_injective⟩
      refine ⟨R, instR, retain', T, hbase, hE, hR, ?_⟩
      exact (D.delete_rowWeights labels signs select hlabel hsign).trans hw

/-- Actual dipole deletion reaches a reduced spherical ribbon on retained original indices,
with exactly the same original row words, basepoints, and quotient-weighted sum. -/
theorem exists_reduced {O : Type} [Fintype O] (words : O → List (SignedLetter X))
    (P : BasedRowRibbon words q) (labels : O → I) (signs : O → Bool)
    (hEuler : P.map.EulerEquality) :
    ∃ (R : Type) (_ : Fintype R) (retain : R ↪ O)
      (T : BasedRowRibbon (fun r ↦ words (retain r)) q),
      (∀ r, T.base r = P.base (retain r)) ∧ T.map.EulerEquality ∧
      T.NoMatchedDipole (fun r ↦ labels (retain r)) (fun r ↦ signs (retain r)) ∧
      (∑ o, P.rowWeight labels signs select o) =
        ∑ r, T.rowWeight (fun r ↦ labels (retain r)) (fun r ↦ signs (retain r)) select r :=
  exists_reduced_aux q select (Fintype.card O) O inferInstance words P labels signs rfl hEuler

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon
