module

public import SmallPresentation.SmallCancellationGeometryBigonFaces
public import SmallPresentation.PermutationCycleRemoval

/-! Exact cell counts and Euler preservation for the constructed bigon suppression. -/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D : Type*} {P : RibbonMap D} (B : Bigon P)

/-- Every old face is either the deleted bigon or one of the actual new faces. -/
noncomputable def faceRemovalEquiv [Finite D] : P.Face ≃ Option B.suppress.Face :=
  (PermutationCycles.removeTwoCycleEquiv P.face B.left B.right B.face_left B.face_right).trans
    B.facesEquiv.symm.optionCongr

/-- The bridged map's removed edge is a single cycle, disjoint from all surviving edges. -/
noncomputable def edgeRemovalEquiv [Finite D] : B.bridged.Edge ≃ Option B.suppress.Edge :=
  PermutationCycles.removeTwoCycleEquiv B.bridged.edge (P.edge B.left) (P.edge B.right)
    B.bridged_edge_mate_left B.bridged_edge_mate_right

/-- Suppression does not change the number of actual vertices. -/
theorem card_vertices [Finite D] :
    Fintype.card B.suppress.Vertex = Fintype.card P.Vertex :=
  Fintype.card_congr B.verticesEquiv

/-- Suppression removes precisely one actual face. -/
theorem card_faces [Finite D] :
    Fintype.card P.Face = Fintype.card B.suppress.Face + 1 := by
  simpa using Fintype.card_congr B.faceRemovalEquiv

/-- Suppression removes precisely one actual edge. -/
theorem card_edges [Fintype D] :
    Fintype.card P.Edge = Fintype.card B.suppress.Edge + 1 := by
  have h := Fintype.card_congr B.edgeRemovalEquiv
  have hb : Fintype.card B.bridged.Edge = Fintype.card P.Edge :=
    P.bridge_card_edges (P.edge B.left) B.right
  simpa only [Fintype.card_option, hb] using h

/-- The actual sphere Euler equation is preserved by suppression, in both directions. -/
theorem sphere_euler_iff [Fintype D] :
    (Fintype.card B.suppress.Vertex + Fintype.card B.suppress.Face =
      Fintype.card B.suppress.Edge + 2) ↔
    (Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) := by
  rw [B.card_vertices, B.card_faces, B.card_edges]
  omega

open Classical in
/-- Suppression removes two actual darts, allowing structural induction on finite diagrams. -/
theorem card_darts [Fintype D] : Fintype.card D = Fintype.card B.Dart + 2 := by
  classical
  have ho := P.card_darts
  have hn := B.suppress.card_darts
  have he := B.card_edges
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
