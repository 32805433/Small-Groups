module

public import SmallPresentation.SmallCancellationDipolePlanarity

/-!
# Dipole topology independent of the coefficient and quotient groups

A row ribbon records only actual indexed signed marker words and their edge and rotation
permutations. Its concrete dipole surgery uses the preceding construction with the trivial
potential. Thus relative pictures can reuse the full topology theorem while preserving their
coefficient equations and nontrivial basepoint data independently.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {O X : Type} (words : O → List (SignedLetter X))

/-- A marked row ribbon with no coefficient or path hypothesis. -/
structure RowRibbon where
  map : RibbonMap (RowDarts words)
  rotation_eq : map.rotation = rowRotation words
  edge_letters : ∀ d, rowRead words (map.edge d) = reverseLetter (rowRead words d)

namespace RowRibbon

variable {words} (P : RowRibbon words)

/-- The trivial potential equips any actual row ribbon with the common deletion coordinates. -/
def trivialBased : BasedRowRibbon words (1 : FreeGroup X →* PUnit) where
  map := P.map
  rotation_eq := P.rotation_eq
  base _ := PUnit.unit
  row_killed _ := Subsingleton.elim _ _
  edge_letters := P.edge_letters
  edge_paths _ := Subsingleton.elim _ _

/-- Actual distinct inverse marker rows joined at one corresponding reverse-position edge. -/
abbrev Dipole := P.trivialBased.Dipole

namespace Dipole

variable {P} (D : P.Dipole)

abbrev Remaining := BasedRowRibbon.Dipole.Remaining D

abbrev RemainingWords : D.Remaining → List (SignedLetter X) := fun o ↦ words o.val

/-- Delete the two actual marker rows and reconnect their bands. -/
noncomputable def delete [Finite O] : RowRibbon D.RemainingWords where
  map := (BasedRowRibbon.Dipole.delete D).map
  rotation_eq := (BasedRowRibbon.Dipole.delete D).rotation_eq
  edge_letters := (BasedRowRibbon.Dipole.delete D).edge_letters

/-- Full-row dipole deletion is spherical independently of any coefficient or quotient data. -/
theorem delete_euler [Finite O] (hplanar : P.map.EulerEquality) :
    D.delete.map.EulerEquality := BasedRowRibbon.Dipole.delete_euler D hplanar

end Dipole
end RowRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
