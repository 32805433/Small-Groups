module

public import SmallPresentation.SmallCancellationDipoleIdentityRibbon
public import SmallPresentation.SmallCancellationDipoleReduction
public import SmallPresentation.SmallCancellationGeometryIdentityPlanarity

/-!
# Reduced based spherical pictures of actual free-group identities

The constructed cap and corridors supply the initial spherical ribbon and its original
quotient basepoints. Actual finite dipole deletion then produces a reduced picture on
retained original occurrences, with exactly the original identity's weighted sum.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I J Q : Type} [Group Q] (paths : WordSection X)
    (rows : I → List (SignedLetter X)) (q : FreeGroup X →* Q)
    (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1)
    (s : Peiffer.Sequence (FreeGroup X) I)
    (hs : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)

theorem basedRowRibbon_euler : (basedRowRibbon paths rows q hkill s hs).map.EulerEquality := by
  apply ((basedRowRibbon paths rows q hkill s hs).map.relabel_euler_iff
    (relatorRibbon paths rows s hs) (discCornerEquiv rows s)
    (indexedEdge_coordinates paths rows s hs)
    (indexedRotation_coordinates paths rows s hs)).mpr
  exact relatorRibbon_euler paths rows s hs

include paths hkill hs in
/-- Every actual identity has a reduced spherical picture retaining its original occurrence
indices, signed row words, quotient conjugators and total selected weighted contribution. -/
theorem exists_reduced_picture (select : I → Option J) :
    ∃ (R : Type) (_ : Fintype R) (retain : R ↪ Fin s.length)
      (T : BasedRowRibbon (fun r ↦ indexedWords rows s (retain r)) q),
      (∀ r, T.base r = q s[retain r].1.1) ∧ T.map.EulerEquality ∧
      T.NoMatchedDipole (fun r ↦ s[retain r].1.2) (fun r ↦ s[retain r].2) ∧
      Peiffer.weights q select s =
        ∑ r, T.rowWeight (fun r ↦ s[retain r].1.2) (fun r ↦ s[retain r].2) select r := by
  obtain ⟨R, inst, retain, T, hbase, hEuler, hred, hw⟩ :=
    BasedRowRibbon.exists_reduced q select (indexedWords rows s)
      (basedRowRibbon paths rows q hkill s hs) (fun i ↦ s[i].1.2) (fun i ↦ s[i].2)
      (basedRowRibbon_euler paths rows q hkill s hs)
  refine ⟨R, inst, retain, T, hbase, hEuler, hred, ?_⟩
  rw [weights_eq_indexed_sum q s select]
  exact hw

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
