module

public import SmallPresentation.SmallCancellationGeometryCounts
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Ribbon maps and labelled bridge surgery

Darts, a fixed-point-free edge involution, and a vertex rotation determine a finite oriented
ribbon map. This module defines its actual face permutation, vertex and face boundary readings,
and relative coefficient equations. It also proves a bridge operation that reconnects two equally
labelled darts while preserving all vertex words. For trivial coefficient groups this preserves
the relative equations automatically.

A ribbon map is not asserted to be planar. The bridge can change face cycles and genus. The
additional planar separation and Euler-preservation lemmas needed for spherical pictures remain
separate obligations; they are not fields supplying a small-cancellation conclusion.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

/-- Combinatorial data of an oriented ribbon map on a dart type. -/
@[ext]
structure RibbonMap (D : Type*) where
  /-- Pair the two ends of each edge. -/
  edge : Equiv.Perm D
  /-- Edge reversal applied twice returns to the original dart. -/
  edge_involutive : Function.Involutive edge
  /-- The two ends are distinct darts, including for loop edges. -/
  edge_ne : ∀ d, edge d ≠ d
  /-- Positive cyclic order of darts at the vertices. -/
  rotation : Equiv.Perm D

namespace RibbonMap

variable {D : Type*} (P : RibbonMap D)

/-- Traverse an edge and then the preceding dart at the other vertex. -/
def face : Equiv.Perm D := P.edge.trans P.rotation.symm

@[simp] theorem face_apply (d : D) : P.face d = P.rotation.symm (P.edge d) := rfl

/-- Actual vertices are cycles of the vertex permutation. -/
abbrev Vertex := Quotient (Equiv.Perm.SameCycle.setoid P.rotation)

/-- Actual faces are cycles of the face permutation. -/
abbrev Face := Quotient (Equiv.Perm.SameCycle.setoid P.face)

/-- Vertex incident to a dart. -/
def vertexOf (d : D) : P.Vertex := Quotient.mk _ d

/-- Face incident to a dart on its chosen side. -/
def faceOf (d : D) : P.Face := Quotient.mk _ d

@[simp] theorem vertexOf_rotation (d : D) : P.vertexOf (P.rotation d) = P.vertexOf d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

@[simp] theorem faceOf_face (d : D) : P.faceOf (P.face d) = P.faceOf d := by
  apply Quotient.sound
  exact (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- The cyclic sequence of all dart occurrences at a chosen based vertex. -/
noncomputable def vertexBoundary (d : D) : List D :=
  List.ofFn (fun k : Fin (Function.minimalPeriod P.rotation d) ↦
    (P.rotation ^ k.val) d)

/-- The cyclic sequence of all dart occurrences at a chosen based face. -/
noncomputable def faceBoundary (d : D) : List D :=
  List.ofFn (fun k : Fin (Function.minimalPeriod P.face d) ↦ (P.face ^ k.val) d)

@[simp] theorem vertexBoundary_length (d : D) :
    (P.vertexBoundary d).length = Function.minimalPeriod P.rotation d := List.length_ofFn

@[simp] theorem faceBoundary_length (d : D) :
    (P.faceBoundary d).length = Function.minimalPeriod P.face d := List.length_ofFn

theorem vertexBoundary_nonempty [Finite D] (d : D) : P.vertexBoundary d ≠ [] := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.rotation.injective.mem_periodicPts d)
  intro he
  have hl := congrArg List.length he
  simp at hl
  omega

theorem faceBoundary_nonempty [Finite D] (d : D) : P.faceBoundary d ≠ [] := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.face.injective.mem_periodicPts d)
  intro he
  have hl := congrArg List.length he
  simp at hl
  omega

/-- Change the pairing by exchanging the ends `a` and `b` while keeping vertex rotations fixed.
This definition makes sense even in the degenerate cases; separate endpoint hypotheses specify
when it reconnects two distinct edges. -/
noncomputable def bridge (a b : D) : RibbonMap D := by
  classical
  let s := Equiv.swap a b
  refine ⟨s.trans (P.edge.trans s), ?_, ?_, P.rotation⟩
  · intro d
    change s (P.edge (s (s (P.edge (s d))))) = d
    rw [Equiv.swap_apply_self, P.edge_involutive, Equiv.swap_apply_self]
  · intro d he
    have h := congrArg s he
    change s (s (P.edge (s d))) = s d at h
    rw [Equiv.swap_apply_self] at h
    exact P.edge_ne (s d) h

@[simp] theorem bridge_rotation (a b : D) : (P.bridge a b).rotation = P.rotation := rfl

open Classical in
@[simp] theorem bridge_edge (a b d : D) :
    (P.bridge a b).edge d = Equiv.swap a b (P.edge (Equiv.swap a b d)) := rfl

@[simp] theorem bridge_vertexBoundary (a b d : D) :
    (P.bridge a b).vertexBoundary d = P.vertexBoundary d := rfl

/-- Reconnecting the same two endpoints twice restores the original ribbon map. -/
theorem bridge_bridge (a b : D) : (P.bridge a b).bridge a b = P := by
  classical
  apply RibbonMap.ext
  · apply Equiv.ext
    intro d
    simp only [bridge_edge, Equiv.swap_apply_self]
  · rfl

/-- In the genuine two-edge case, the first endpoint is paired with the old mate of the second. -/
theorem bridge_edge_left (a b : D) (hedges : P.edge b ≠ a) :
    (P.bridge a b).edge a = P.edge b := by
  classical
  rw [bridge_edge, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hedges (P.edge_ne b)

/-- The second endpoint is paired with the old mate of the first. -/
theorem bridge_edge_right (a b : D) (hedges : P.edge b ≠ a) :
    (P.bridge a b).edge b = P.edge a := by
  classical
  rw [bridge_edge, Equiv.swap_apply_right]
  apply Equiv.swap_apply_of_ne_of_ne (P.edge_ne a)
  intro h
  apply hedges
  rw [← h, P.edge_involutive]

/-- The old mate of the first endpoint is now paired with the second endpoint. -/
theorem bridge_edge_mate_left (a b : D) (hedges : P.edge b ≠ a) :
    (P.bridge a b).edge (P.edge a) = b := by
  have h := bridge_edge_right P a b hedges
  rw [← h]
  exact (P.bridge a b).edge_involutive b

/-- All other edges retain their pairing. -/
theorem bridge_edge_unchanged (a b d : D) (hda : d ≠ a) (hdb : d ≠ b)
    (heda : P.edge d ≠ a) (hedb : P.edge d ≠ b) : (P.bridge a b).edge d = P.edge d := by
  classical
  rw [bridge_edge, Equiv.swap_apply_of_ne_of_ne hda hdb,
    Equiv.swap_apply_of_ne_of_ne heda hedb]

end RibbonMap

/-- A generator with a choice of transverse orientation. -/
abbrev SignedLetter (X : Type*) := X × Bool

/-- Reverse the transverse orientation of a labelled arc. -/
def reverseLetter {X : Type*} (x : SignedLetter X) : SignedLetter X := (x.1, !x.2)

@[simp] theorem reverseLetter_reverseLetter {X : Type*} (x : SignedLetter X) :
    reverseLetter (reverseLetter x) = x := by cases x; simp [reverseLetter]

/-- Labels on the arcs and the corners of a ribbon map, with the edge orientation law. -/
structure RibbonLabelling {D : Type*} (P : RibbonMap D) (X H : Type*) where
  arc : D → SignedLetter X
  corner : D → H
  edge_arc : ∀ d, arc (P.edge d) = reverseLetter (arc d)

namespace RibbonLabelling

variable {D X H : Type*} {P : RibbonMap D} (L : RibbonLabelling P X H)

/-- Read the based vertex word as the ordered free-letter/coefficient pairs. -/
noncomputable def vertexWord (d : D) : List (SignedLetter X × H) :=
  (P.vertexBoundary d).map (fun e ↦ (L.arc e, L.corner e))

/-- Read a face coefficient product. A face traverses vertex corners backwards, so the
coefficients are inverted; this matters for noncommutative coefficient groups. -/
noncomputable def faceValue [Group H] (d : D) : H :=
  ((P.faceBoundary d).map (fun e ↦ (L.corner e)⁻¹)).prod

open Classical in
private theorem arc_swap {a b : D} (h : L.arc a = L.arc b) (d : D) :
    L.arc (Equiv.swap a b d) = L.arc d := by
  classical
  by_cases ha : d = a
  · subst d
    simpa using h.symm
  · by_cases hb : d = b
    · subst d
      simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A bridge between equally labelled ends preserves arc labels and every corner label. -/
noncomputable def bridge (a b : D) (h : L.arc a = L.arc b) :
    RibbonLabelling (P.bridge a b) X H where
  arc := L.arc
  corner := L.corner
  edge_arc d := by
    classical
    rw [RibbonMap.bridge_edge, L.arc_swap h, L.edge_arc, L.arc_swap h]

@[simp] theorem bridge_vertexWord (a b : D) (h : L.arc a = L.arc b) (d : D) :
    (L.bridge a b h).vertexWord d = L.vertexWord d := rfl

@[simp] theorem bridge_vertexWord_length (a b : D) (h : L.arc a = L.arc b) (d : D) :
    ((L.bridge a b h).vertexWord d).length = (L.vertexWord d).length := rfl

/-- Relator membership is preserved literally, without changing the relator family or labels. -/
theorem bridge_relator_membership {I : Type*} (relators : I → List (SignedLetter X × H))
    (hrel : ∀ d, ∃ i, L.vertexWord d = relators i)
    (a b : D) (h : L.arc a = L.arc b) :
    ∀ d, ∃ i, (L.bridge a b h).vertexWord d = relators i := hrel

end RibbonLabelling

/-- A labelled relative ribbon map with an outer face, relator labels, and all inner coefficient
relations. Relator families here are oriented and based; cyclic rotations can be indexed explicitly.
No sphere or planarity property is asserted by this data type. -/
structure RelativeRibbon {D : Type*} (X H I : Type*) [Group H]
    (relators : I → List (SignedLetter X × H)) where
  map : RibbonMap D
  labelling : RibbonLabelling map X H
  outside : D
  relator : D → I
  relator_word : ∀ d, labelling.vertexWord d = relators (relator d)
  inner_equation : ∀ d, ¬map.face.SameCycle outside d → labelling.faceValue d = 1

namespace RelativeRibbon

variable {D X H I : Type*} [Group H] {relators : I → List (SignedLetter X × H)}
variable (P : RelativeRibbon (D := D) X H I relators)

/-- For ordinary pictures, the bridge preserves every relative labelling axiom. A planar
application must additionally control the face change; this construction asserts no genus claim. -/
noncomputable def bridge [Subsingleton H] (a b : D)
    (h : P.labelling.arc a = P.labelling.arc b) : RelativeRibbon (D := D) X H I relators where
  map := P.map.bridge a b
  labelling := P.labelling.bridge a b h
  outside := P.outside
  relator := P.relator
  relator_word := P.relator_word
  inner_equation _ _ := Subsingleton.elim _ _

@[simp] theorem bridge_relator [Subsingleton H] (a b : D)
    (h : P.labelling.arc a = P.labelling.arc b) (d : D) :
    (P.bridge a b h).relator d = P.relator d := rfl

end RelativeRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
