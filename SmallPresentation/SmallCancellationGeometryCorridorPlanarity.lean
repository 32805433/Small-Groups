module

public import SmallPresentation.SmallCancellationGeometryCorridorRotation
public import SmallPresentation.SmallCancellationGeometryCorridorRelabel
public import SmallPresentation.SmallCancellationGeometryPairingFacesCounts

/-!
# Euler equality for the actual corridor ribbon

The cap ribbon is spherical by its noncrossing construction. The precise typed
corridor rotation is obtained from its circle by genuine vertex splits, so all
of its components are spherical, including the disconnected components created
by cuts. No planarity assumption is added to the incidence data.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open PermutationCycles RelationCoordinates

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))

theorem ribbon_euler (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    Fintype.card (ribbon paths rows s h).Vertex +
        Fintype.card (ribbon paths rows s h).Face =
      Fintype.card (ribbon paths rows s h).Edge +
        2 * Fintype.card (ribbon paths rows s h).Component := by
  let P := ribbon paths rows s h
  by_cases hn : 0 < (boundary paths rows s).length
  · have hs : Subsingleton P.Component := ⟨fun x y ↦ by
      induction x using Quotient.inductionOn with | h d =>
      induction y using Quotient.inductionOn with | h e =>
      apply Quotient.sound
      apply P.component_of_vertexCycle
      exact finRotate_sameCycle d e⟩
    let := hs
    let : Nonempty P.Component := ⟨Quotient.mk _ ⟨0, hn⟩⟩
    have hc : Fintype.card P.Component = 1 := by
      exact Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ ⟨0, hn⟩, fun _ ↦ Subsingleton.elim _ _⟩
    rw [hc]
    exact (pairing paths rows s h).sphere_euler hn
  · have hz : (boundary paths rows s).length = 0 := by omega
    let : IsEmpty (Fin (boundary paths rows s).length) := ⟨fun d ↦ by have hd := d.isLt; omega⟩
    let : IsEmpty P.Vertex := ⟨fun q ↦ Quotient.inductionOn q isEmptyElim⟩
    let : IsEmpty P.Face := ⟨fun q ↦ Quotient.inductionOn q isEmptyElim⟩
    let : IsEmpty P.Edge := ⟨fun q ↦ Quotient.inductionOn q isEmptyElim⟩
    let : IsEmpty P.Component := ⟨fun q ↦ Quotient.inductionOn q isEmptyElim⟩
    simp only [Fintype.card_eq_zero, Nat.zero_add, Nat.mul_zero]

/-- The concrete intermediate graph, with cap edges and corridor/relator vertices,
satisfies the spherical Euler equation componentwise in total. -/
theorem corridorRibbon_euler (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    Fintype.card (corridorRibbon paths rows s h).Vertex +
        Fintype.card (corridorRibbon paths rows s h).Face =
      Fintype.card (corridorRibbon paths rows s h).Edge +
        2 * Fintype.card (corridorRibbon paths rows s h).Component := by
  let P := ribbon paths rows s h
  let e := dartCoordinates paths rows s
  let Q := P.withRotation (transport e (corridorRotation paths rows s))
  have hQ := P.splitRefinement_preserves_euler (corridorRotation_refinement paths rows s)
    (ribbon_euler paths rows s h)
  apply ((corridorRibbon paths rows s h).relabel_euler_iff Q e ?_ ?_).mpr hQ
  · intro d
    simp only [corridorRibbon, capIdentification, e, Equiv.trans_apply,
      Equiv.apply_symm_apply]
    rfl
  · intro d
    exact (transport_at e (corridorRotation paths rows s) d).symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
