module

public import SmallPresentation.SmallCancellationGeometryCorridorBlock
public import SmallPresentation.SmallCancellationGeometryIdentityRibbon

/-!
# The actual corridor and relator vertex rotation

The literal conjugator blocks refine the original boundary circle into the relator
cycles and the degree-two corridor vertices. Empty blocks contribute no vertices.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open PermutationCycles RelationCoordinates

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))

def blockCorridorRotation (a : Peiffer.Occurrence (FreeGroup X) I) :
    Equiv.Perm (BlockDart paths rows a) :=
  corridorPermutation (paths.word a.1.1).length (orientedWord (rows a.1.2) a.2).length

theorem blockCoordinates_corridor (a : Peiffer.Occurrence (FreeGroup X) I) :
    blockCoordinates paths rows a =
      (corridorCoordinates (paths.word a.1.1).length
        (orientedWord (rows a.1.2) a.2).length).trans
        (finCongr (by simp [block, Nat.add_left_comm, Nat.two_mul])) := by
  ext d
  rcases d with d | (d | d) <;> rfl

theorem blockCorridorRotation_refinement (a : Peiffer.Occurrence (FreeGroup X) I) :
    SplitRefinement (finRotate (block paths rows a).length)
      (transport (blockCoordinates paths rows a) (blockCorridorRotation paths rows a)) := by
  let e := finCongr (by simp [block, Nat.add_left_comm, Nat.two_mul] :
    (orientedWord (rows a.1.2) a.2).length + 2 * (paths.word a.1.1).length =
      (block paths rows a).length)
  have hh := (corridorPermutation_refinement (paths.word a.1.1).length
    (orientedWord (rows a.1.2) a.2).length).transport e
  have he : transport e (finRotate _) = finRotate (block paths rows a).length :=
    transport_eq _ _ _ (finRotate_finCongr _)
  rw [he, transport_trans] at hh
  rw [blockCoordinates_corridor]
  exact hh

def corridorRotation : (s : Peiffer.Sequence (FreeGroup X) I) →
    Equiv.Perm (Darts paths rows s)
  | [] => Equiv.refl _
  | a :: s => Equiv.sumCongr (blockCorridorRotation paths rows a) (corridorRotation s)

theorem corridorRotation_refinement (s : Peiffer.Sequence (FreeGroup X) I) :
    SplitRefinement (finRotate (boundary paths rows s).length)
      (transport (dartCoordinates paths rows s) (corridorRotation paths rows s)) := by
  induction s with
  | nil =>
    have he : transport (dartCoordinates paths rows []) (corridorRotation paths rows []) =
        finRotate (boundary paths rows []).length := by ext d; exact Fin.elim0 d
    rw [he]
    exact .refl _
  | cons a s ih =>
    let e := finCongr (by simp : (block paths rows a).length +
      (boundary paths rows s).length = (boundary paths rows (a :: s)).length)
    have hh := ((blockCorridorRotation_refinement paths rows a).append ih).transport e
    have he : transport e (finRotate _) = finRotate (boundary paths rows (a :: s)).length :=
      transport_eq _ _ _ (finRotate_finCongr _)
    rw [he, transport_trans] at hh
    convert hh using 1
    apply transport_eq
    intro d
    change (finSumFinEquiv.trans e)
        ((Equiv.sumCongr (blockCoordinates paths rows a) (dartCoordinates paths rows s))
          (Equiv.sumCongr (blockCorridorRotation paths rows a) (corridorRotation paths rows s) d)) =
      transport (finSumFinEquiv.trans e) _
        ((finSumFinEquiv.trans e)
          ((Equiv.sumCongr (blockCoordinates paths rows a) (dartCoordinates paths rows s)) d))
    rw [transport_at]
    congr 1
    rcases d with d | d <;>
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, transport_at]

/-- At a marked relator dart the intermediate rotation is exactly the original row order. -/
theorem corridorRotation_disc (s : Peiffer.Sequence (FreeGroup X) I) (d : DiscDarts rows s) :
    corridorRotation paths rows s (discInclusion paths rows s d) =
      discInclusion paths rows s (discRotation rows s d) := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · rfl
    · exact congrArg Sum.inr (ih d)

/-- Every unmarked dart is a degree-two corridor vertex with the prescribed reverse partner. -/
theorem corridorRotation_off_disc (s : Peiffer.Sequence (FreeGroup X) I)
    (d : Darts paths rows s) (hd : corridorIdentification paths rows s d ≠ d) :
    corridorRotation paths rows s d = corridorIdentification paths rows s d := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with (d | (d | d)) | d
    · rfl
    · exact (hd rfl).elim
    · rfl
    · exact congrArg Sum.inr (ih d (fun he ↦ hd (congrArg Sum.inr he)))

/-- The actual intermediate ribbon before suppressing the corridor vertices. -/
noncomputable def corridorRibbon (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    RibbonMap (Darts paths rows s) where
  edge := capIdentification paths rows s h
  edge_involutive := capIdentification_involutive paths rows s h
  edge_ne := capIdentification_ne paths rows s h
  rotation := corridorRotation paths rows s

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
