module

public import SmallPresentation.SmallCancellationGeometryIdentityVertices
public import SmallPresentation.PermutationCycleProductsFin

/-! The exact based vertex word of the identity ribbon, at its original zero corner. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates PermutationCycles

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))
    (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)

theorem vertexBoundary_at_zero (i : Fin s.length)
    (hp : 0 < (orientedWord (rows s[i].1.2) s[i].2).length) :
    (relatorRibbon paths rows s h).vertexBoundary (discAt rows s i ⟨0, hp⟩) =
      List.ofFn (fun j : Fin (orientedWord (rows s[i].1.2) s[i].2).length ↦ discAt rows s i j) := by
  let : NeZero (orientedWord (rows s[i].1.2) s[i].2).length := ⟨Nat.ne_of_gt hp⟩
  have hh := cycleBoundary_map_injective
    (finRotate (orientedWord (rows s[i].1.2) s[i].2).length) (discRotation rows s)
    (discAt rows s i) (discAt_injective rows s i) (fun j ↦ (discRotation_at rows s i j).symm) 0
  rw [cycleBoundary_finRotate_zero, List.map_ofFn] at hh
  exact hh.symm

theorem vertex_read_at_zero (i : Fin s.length)
    (hp : 0 < (orientedWord (rows s[i].1.2) s[i].2).length) :
    ((relatorRibbon paths rows s h).vertexBoundary (discAt rows s i ⟨0, hp⟩)).map
      (discRead paths rows s) = orientedWord (rows s[i].1.2) s[i].2 := by
  rw [vertexBoundary_at_zero, List.map_ofFn]
  exact disc_row_read rows paths s i

theorem discRead_mem_oriented (i : Fin s.length) (d : DiscDarts rows s)
    (hd : discOccurrence rows s d = i) :
    discRead paths rows s d ∈ orientedWord (rows s[i].1.2) s[i].2 := by
  obtain ⟨j, k, rfl⟩ := exists_discAt rows s d
  rw [discOccurrence_at] at hd
  subst j
  rw [discRead_at]
  exact List.getElem_mem k.isLt

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
