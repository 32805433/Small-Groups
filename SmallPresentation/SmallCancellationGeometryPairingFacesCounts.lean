module

public import SmallPresentation.SmallCancellationGeometryPairingFaces
public import SmallPresentation.PermutationCycleCounts

/-!
# Sphere Euler characteristic of the actual boundary-pairing ribbon

The face-count induction uses the explicit bijection of face cycles under cap insertion.
No genus or Euler hypothesis is supplied. The empty ribbon is treated separately, since its
ambient empty-disc region has no dart and therefore is absent from the face-cycle quotient.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing

variable {X : Type*}

/-- The initial cap has precisely two actual face cycles. -/
theorem card_initial_faces (x : X) (sign : Bool) (old : BoundaryPairing ([] :
    List (SignedLetter X))) :
    Fintype.card (BoundaryPairing.insert [] [] x sign old).ribbon.Face = 2 := by
  let P := BoundaryPairing.insert [] [] x sign old
  let e : P.ribbon.Face ≃ Fin 2 :=
    (PermutationCycles.conjugateEquiv P.ribbon.face (Equiv.refl _) (Equiv.refl _)
      (fun d ↦ by
        change P.ribbon.face d = d
        exact congrArg (fun σ : Equiv.Perm (Fin 2) ↦ σ d)
          (initial_face_identity x sign old))).trans
      PermutationCycles.identityCycles
  simpa using Fintype.card_congr e

/-- Every nonempty cap pairing has one more actual face than recorded arcs. -/
theorem card_faces {w : List (SignedLetter X)} (P : BoundaryPairing w) (hn : 0 < w.length) :
    Fintype.card P.ribbon.Face = P.arcs.length + 1 := by
  induction P with
  | empty => simp at hn
  | insert before after x sign old ih =>
    by_cases hzero : (before ++ after).length = 0
    · have hb : before = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_append] at hzero
        omega
      have ha : after = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_append] at hzero
        omega
      subst before
      subst after
      have harcs : old.arcs.length = 0 := by
        have h := old.twice_arcs_length
        simp only [List.nil_append, List.length_nil] at h
        omega
      rw [card_initial_faces]
      simp [arcs, harcs]
    · have hpos : 0 < (before ++ after).length := Nat.pos_of_ne_zero hzero
      rw [card_insertedFaces before after x sign old hpos, ih hpos]
      simp [arcs, Nat.add_assoc]

/-- All boundary darts belong to the same actual vertex cycle. -/
theorem card_vertices {w : List (SignedLetter X)} (P : BoundaryPairing w)
    (hn : 0 < w.length) : Fintype.card P.ribbon.Vertex = 1 := by
  let : Fintype (PermutationCycles.Cycles (finRotate w.length)) := Fintype.ofFinite _
  exact PermutationCycles.card_finRotateCycles w.length hn

/-- Recorded arcs are in bijective count with actual edge cycles. -/
theorem card_edges {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    Fintype.card P.ribbon.Edge = P.arcs.length := by
  have hd := P.ribbon.card_darts
  have ha := P.twice_arcs_length
  simp only [Fintype.card_fin] at hd
  omega

/-- The actual nonempty pairing ribbon has the sphere Euler characteristic. -/
theorem sphere_euler {w : List (SignedLetter X)} (P : BoundaryPairing w)
    (hn : 0 < w.length) :
    Fintype.card P.ribbon.Vertex + Fintype.card P.ribbon.Face =
      Fintype.card P.ribbon.Edge + 2 := by
  rw [P.card_vertices hn, P.card_faces hn, P.card_edges]
  omega

/-- All three dart-defined cell counts vanish for the empty matching. -/
theorem empty_counts :
    Fintype.card (BoundaryPairing.empty (X := X)).ribbon.Vertex = 0 ∧
    Fintype.card (BoundaryPairing.empty (X := X)).ribbon.Edge = 0 ∧
    Fintype.card (BoundaryPairing.empty (X := X)).ribbon.Face = 0 := by
  have hv : IsEmpty (BoundaryPairing.empty (X := X)).ribbon.Vertex :=
    ⟨fun q ↦ Quotient.inductionOn q (fun d ↦ d.elim0)⟩
  exact ⟨Fintype.card_eq_zero, by rw [card_edges]; rfl, card_empty_faces⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing
