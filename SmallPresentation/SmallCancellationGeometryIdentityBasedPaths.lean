module

public import SmallPresentation.SmallCancellationGeometryIdentityVertices

/-!
# Literal based paths and their quotient weights

The path to a marked relator disc in the cut-open boundary first reads all preceding
conjugate blocks and then that occurrence's chosen conjugator. Its exact free-group value
is recorded. In every quotient killing the attaching rows this path has precisely the
original conjugator's value. Thus labels, signs and group-ring weights of occurrences
are retained by the construction, without claiming a change-of-spray theorem.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I Q : Type} [Group Q] (paths : WordSection X)
  (rows : I → List (SignedLetter X))

/-- The literal cut-open path from the ambient basepoint to the marked disc corner. -/
def basedPath (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) :
    List (SignedLetter X) :=
  boundary paths rows (s.take i.val) ++ paths.word s[i].1.1

/-- Its free-group value remembers the ordered preceding occurrences. -/
theorem basedPath_evaluates (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) :
    FreeGroup.mk (basedPath paths rows s i) =
      Peiffer.evaluation (fun j ↦ FreeGroup.mk (rows j)) (s.take i.val) * s[i].1.1 := by
  rw [basedPath, ← FreeGroup.mul_mk, boundary_evaluates, paths.evaluates]

/-- The based path is an actual prefix at the marked corner of the expanded boundary. -/
theorem boundary_at_basedPath (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) :
    boundary paths rows s = basedPath paths rows s i ++
      orientedWord (rows s[i].1.2) s[i].2 ++ FreeGroup.invRev (paths.word s[i].1.1) ++
        boundary paths rows (s.drop (i.val + 1)) := by
  have hs : s.take i.val ++ s[i] :: s.drop (i.val + 1) = s := by
    calc
      _ = (s.take i.val ++ [s[i]]) ++ s.drop (i.val + 1) := by simp
      _ = s := by
        simp only [Fin.getElem_fin]
        rw [List.take_append_getElem i.isLt, List.take_append_drop]
  have hh := congrArg (boundary paths rows) hs
  rw [boundary_append, boundary_cons] at hh
  simpa only [basedPath, block, List.append_assoc] using hh.symm

/-- A killed-relator quotient kills every complete preceding conjugate block. -/
theorem quotient_evaluation (q : FreeGroup X →* Q) (hkill : ∀ j, q (FreeGroup.mk (rows j)) = 1)
    (s : Peiffer.Sequence (FreeGroup X) I) :
    q (Peiffer.evaluation (fun j ↦ FreeGroup.mk (rows j)) s) = 1 := by
  induction s with
  | nil => exact q.map_one
  | cons a s ih =>
    change q (Peiffer.term (fun j ↦ FreeGroup.mk (rows j)) a *
      Peiffer.evaluation (fun j ↦ FreeGroup.mk (rows j)) s) = 1
    rw [map_mul, Peiffer.quotient_term _ q hkill, ih, one_mul]

/-- The actual marked based path has exactly the original occurrence's quotient weight. -/
theorem basedPath_quotient (q : FreeGroup X →* Q) (hkill : ∀ j, q (FreeGroup.mk (rows j)) = 1)
    (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) :
    q (FreeGroup.mk (basedPath paths rows s i)) = q s[i].1.1 := by
  rw [basedPath_evaluates, map_mul, quotient_evaluation rows q hkill, one_mul]

/-- Extend the marked path to any specified corner by the literal prefix of its signed row. -/
def cornerPath (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) (j : ℕ) :
    List (SignedLetter X) :=
  basedPath paths rows s i ++ (orientedWord (rows s[i].1.2) s[i].2).take j

/-- The corner correction is exactly the cyclic-prefix correction required in dipole reading. -/
theorem cornerPath_quotient (q : FreeGroup X →* Q)
    (hkill : ∀ j, q (FreeGroup.mk (rows j)) = 1)
    (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) (j : ℕ) :
    q (FreeGroup.mk (cornerPath paths rows s i j)) =
      q s[i].1.1 * q (FreeGroup.mk ((orientedWord (rows s[i].1.2) s[i].2).take j)) := by
  rw [cornerPath, ← FreeGroup.mul_mk, map_mul, basedPath_quotient paths rows q hkill]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
