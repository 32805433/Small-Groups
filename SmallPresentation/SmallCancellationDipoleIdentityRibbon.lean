module

public import SmallPresentation.SmallCancellationDipoleBookkeeping
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Based row ribbons of actual identity sequences

The row-indexed interface used by dipole deletion is obtained from the constructed
identity-boundary ribbon by its proved indexed-corner equivalence. Both the edge pairing
and vertex rotation are the original ones in these new coordinates.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I Q : Type} [Group Q] (paths : WordSection X)
    (rows : I → List (SignedLetter X)) (q : FreeGroup X →* Q)
    (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1)
    (s : Peiffer.Sequence (FreeGroup X) I)
    (hs : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)

abbrev indexedWords (i : Fin s.length) : List (SignedLetter X) :=
  orientedWord (rows s[i].1.2) s[i].2

theorem weights_eq_indexed_sum {J : Type} (label : I → Option J) :
    Peiffer.weights q label s = ∑ i : Fin s.length, Peiffer.weight q label s[i] := by
  exact (Fin.sum_univ_fun_getElem s (Peiffer.weight q label)).symm

noncomputable def indexedEdge : Equiv.Perm (RowDarts (indexedWords rows s)) :=
  (discCornerEquiv rows s).trans
    ((relatorRibbon paths rows s hs).edge.trans (discCornerEquiv rows s).symm)

theorem indexedEdge_coordinates (d : RowDarts (indexedWords rows s)) :
    discCornerEquiv rows s (indexedEdge paths rows s hs d) =
      (relatorRibbon paths rows s hs).edge (discCornerEquiv rows s d) := by
  simp only [indexedEdge, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem indexedRotation_coordinates (d : RowDarts (indexedWords rows s)) :
    discCornerEquiv rows s (rowRotation (indexedWords rows s) d) =
      (relatorRibbon paths rows s hs).rotation (discCornerEquiv rows s d) := by
  exact (discRotation_at rows s d.1 d.2).symm

theorem indexedRead_coordinates (d : RowDarts (indexedWords rows s)) :
    discRead paths rows s (discCornerEquiv rows s d) = rowRead (indexedWords rows s) d :=
  discRead_at paths rows s d.1 d.2

include hkill in
theorem indexedPotential_coordinates (d : RowDarts (indexedWords rows s)) :
    discPotential paths rows q s (discCornerEquiv rows s d) =
      rowPotential (indexedWords rows s) q (fun i ↦ q s[i].1.1) d :=
  discPotential_at paths rows q hkill s d.1 d.2

/-- The actual relator ribbon in original occurrence/corner coordinates, with proved paths. -/
noncomputable def basedRowRibbon : BasedRowRibbon (indexedWords rows s) q where
  map := {
    edge := indexedEdge paths rows s hs
    edge_involutive := by
      intro d
      apply (discCornerEquiv rows s).injective
      rw [indexedEdge_coordinates, indexedEdge_coordinates,
        (relatorRibbon paths rows s hs).edge_involutive]
    edge_ne := by
      intro d he
      have hh := congrArg (discCornerEquiv rows s) he
      rw [indexedEdge_coordinates] at hh
      exact (relatorRibbon paths rows s hs).edge_ne _ hh
    rotation := rowRotation (indexedWords rows s)
  }
  rotation_eq := rfl
  base i := q s[i].1.1
  row_killed i := orientedWord_quotient rows q hkill s[i].1.2 s[i].2
  edge_letters d := by
    rw [← indexedRead_coordinates paths rows s, indexedEdge_coordinates]
    simpa only [indexedRead_coordinates] using
      relatorRibbon_edge_read paths rows s hs (discCornerEquiv rows s d)
  edge_paths d := by
    rw [← indexedPotential_coordinates paths rows q hkill s,
      indexedEdge_coordinates]
    simpa only [indexedPotential_coordinates paths rows q hkill, indexedRead_coordinates] using
      relatorRibbon_edge_potential paths rows q hkill s hs (discCornerEquiv rows s d)

namespace IndexedDipole

variable {paths rows s hs}

/-- An actual indexed dipole supplies exactly the geometric anchor required by deletion. -/
noncomputable def toRowDipole (D : IndexedDipole paths rows s hs) :
    (basedRowRibbon paths rows q hkill s hs).Dipole where
  first := D.first
  second := D.second
  distinct := D.first_ne_second
  inverse_words := D.inverse_rows
  anchor := D.firstCorner
  edge_anchor := by
    apply (discCornerEquiv rows s).injective
    change discCornerEquiv rows s (indexedEdge paths rows s hs _) = _
    rw [indexedEdge_coordinates]
    change (relatorRibbon paths rows s hs).edge (discAt rows s D.first D.firstCorner) = _
    rw [D.edge_eq]
    apply congrArg (discAt rows s D.second)
    apply Fin.ext
    change D.secondCorner.val =
      (BasedRowRibbon.inverseCorner (words := indexedWords rows s) D.inverse_rows D.firstCorner).val
    rw [BasedRowRibbon.inverseCorner_val]
    change D.secondCorner.val =
      (orientedWord (rows s[D.first].1.2) s[D.first].2).length - (D.firstCorner.val + 1)
    have hh := D.reverse_positions
    have hl := orientedWord_length (rows s[D.first].1.2) s[D.first].2
    omega

/-- The actual finite deletion removes exactly two original occurrence indices. -/
theorem delete_card (D : IndexedDipole paths rows s hs) :
    s.length = Nat.card (D.toRowDipole q hkill).Remaining + 2 := by
  classical
  change s.length = Nat.card (RowDeletion.Remaining D.first D.second) + 2
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    RowDeletion.card_remaining D.first D.second D.first_ne_second

/-- Removing the actual two rows preserves the original quotient-weighted identity sum. -/
theorem delete_weight {J : Type} (D : IndexedDipole paths rows s hs) (label : I → Option J) :
    (∑ i : Fin s.length, Peiffer.weight q label s[i]) =
      ∑ i : (D.toRowDipole q hkill).Remaining, Peiffer.weight q label s[i.val] := by
  classical
  exact RowDeletion.sum_preserved D.first D.second D.first_ne_second
    (fun i ↦ Peiffer.weight q label s[i]) (D.weight_cancel q hkill label)

theorem delete_weights {J : Type} (D : IndexedDipole paths rows s hs) (label : I → Option J) :
    Peiffer.weights q label s =
      ∑ i : (D.toRowDipole q hkill).Remaining, Peiffer.weight q label s[i.val] := by
  rw [weights_eq_indexed_sum q s label]
  exact D.delete_weight q hkill label

end IndexedDipole

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
