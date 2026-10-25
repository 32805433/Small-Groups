module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionStep
public import SmallPresentation.SmallCancellationGeometryRelativeExtractionReadings

/-!
# Terminating extraction of an all-new relative picture

Normalize actual old factor discs by adjacent-marker cancellation. At each step retain an
actual new-containing component with one possible outside region. The finite incidence count
strictly decreases. The resulting embedding preserves every retained new row word and every
quotient path potential, as well as its original incidence label.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

universe u
variable {D : Type u} {X H Q : Type*} [Finite D] [Group H] [Group Q]
    {P : RibbonMap D} {L : RibbonLabelling P X H} {q : H →* Q}

/-- An actual all-new spherical subpicture obtained by old-disc normalization. The inclusion
records original incidences; it is not asserted to preserve edges reconnected by surgery. -/
structure OldDiscExtraction (S : OldDiscSystem L) (F : CornerPotential L q) where
  Dart : Type u
  [finite : Finite Dart]
  map : RibbonMap Dart
  label : RibbonLabelling map X H
  potential : CornerPotential label q
  inclusion : Dart ↪ D
  outside : Dart
  connected : map.Connected
  euler : map.EulerEquality
  regions : ∀ d, ¬map.face.SameCycle outside d → label.faceValue d = 1
  new : ∀ d, ¬S.old (inclusion d)
  arc : ∀ d, label.arc d = L.arc (inclusion d)
  corner : ∀ d, label.corner d = L.corner (inclusion d)
  rotation : ∀ d, inclusion (map.rotation d) = P.rotation (inclusion d)
  forward : ∀ d, label.vertexWord d = L.vertexWord (inclusion d)
  backward : ∀ d, label.reverseVertexWord d = L.reverseVertexWord (inclusion d)
  value : ∀ d, potential.value d = F.value (inclusion d)

attribute [instance] OldDiscExtraction.finite

namespace OldDiscExtraction

variable {S : OldDiscSystem L} {F : CornerPotential L q} (W : OldDiscExtraction S F)

omit [Finite D] in
/-- A retained new vertex is the entire original vertex, with its original cyclic order. -/
theorem vertexBoundary (d : W.Dart) :
    (W.map.vertexBoundary d).map W.inclusion = P.vertexBoundary (W.inclusion d) :=
  PermutationCycles.cycleBoundary_map_injective W.map.rotation P.rotation W.inclusion
    W.inclusion.injective W.rotation d

/-- The inclusion identifies actual vertices, independently of any repeated row labels. -/
theorem sameVertex_iff (d e : W.Dart) :
    W.map.rotation.SameCycle d e ↔ P.rotation.SameCycle (W.inclusion d) (W.inclusion e) := by
  rw [← W.map.mem_vertexBoundary_iff, ← P.mem_vertexBoundary_iff, ← W.vertexBoundary]
  exact (List.mem_map_of_injective W.inclusion.injective).symm

end OldDiscExtraction

namespace OldDiscSystem

/-- Every connected spherical mixed picture containing a new vertex has an actual all-new
extraction. This is finite surgery, with no abstract diagram-realization assumption. -/
theorem exists_extraction (D : Type u) [Fintype D] (P : RibbonMap D)
    (L : RibbonLabelling P X H) (S : OldDiscSystem L) (F : CornerPotential L q)
    (outside : D) (hc : P.Connected) (hE : P.EulerEquality)
    (hregions : ∀ d, ¬P.face.SameCycle outside d → L.faceValue d = 1)
    (n : D) (hn : ¬S.old n) : Nonempty (OldDiscExtraction S F) := by
  classical
  by_cases hall : ∀ d, ¬S.old d
  · exact ⟨{
      Dart := D
      map := P
      label := L
      potential := F
      inclusion := Function.Embedding.refl D
      outside := outside
      connected := hc
      euler := hE
      regions := hregions
      new := hall
      arc := fun _ ↦ rfl
      corner := fun _ ↦ rfl
      rotation := fun _ ↦ rfl
      forward := fun _ ↦ rfl
      backward := fun _ ↦ rfl
      value := fun _ ↦ rfl }⟩
  · obtain ⟨a, ha⟩ := not_forall.mp hall
    have ha : S.old a := not_not.mp ha
    obtain ⟨d, had, hdnegative⟩ := (S.disc a ha).exists_negative
    have hd : S.old d := (S.constant had).mp ha
    let C := S.cancellation d hd hdnegative
    let harc := S.cancellation_arc d hd hdnegative
    let hleft := S.cancellation_corner d hd hdnegative
    let M := C.labelling L harc
    let T := S.cancel d hd hdnegative
    let K := F.cancel C harc hleft
    let n' := S.survivingNew d hd hdnegative n hn
    obtain ⟨m, o, hm, hmo, hfaces⟩ := C.extract_regions L harc hleft outside hregions T
      hc hE (S.disc d hd).product n' hn
    let p := C.delete.SameComponent m
    let he := C.delete.component_membership_edge m
    let hr := C.delete.component_membership_rotation m
    let E := {e : C.Dart // p e}
    let R := C.delete.restrict p he hr
    let N := M.restrict p he hr
    let U := T.restrict p he hr
    let V := K.restrict p he hr
    let n'' : E := ⟨m, Relation.EqvGen.refl _⟩
    let o' : E := ⟨o, hmo⟩
    have hRc : R.Connected := C.delete.componentRibbon_connected m
    have hRE : R.EulerEquality := C.delete.restrict_euler p he hr (C.delete_euler hE)
    have hregions' : ∀ e, ¬R.face.SameCycle o' e → N.faceValue e = 1 := by
      intro e hne
      rw [M.restrict_faceValue p he hr]
      apply hfaces e.val e.property
      intro h
      exact hne ((C.delete.restrict_sameFace_iff p he hr o' e).mpr h)
    obtain ⟨W⟩ := exists_extraction E R N U V o' hRc hRE hregions' n'' hm
    refine ⟨{
      Dart := W.Dart
      map := W.map
      label := W.label
      potential := W.potential
      inclusion := W.inclusion.trans
        (⟨fun e ↦ e.val.val, fun e f h ↦ Subtype.ext (Subtype.ext h)⟩ : E ↪ D)
      outside := W.outside
      connected := W.connected
      euler := W.euler
      regions := W.regions
      new := W.new
      arc := ?_
      corner := ?_
      rotation := ?_
      forward := ?_
      backward := ?_
      value := ?_ }⟩
    · intro e
      exact W.arc e
    · intro e
      rw [W.corner e]
      exact S.cancel_new_corner d hd hdnegative (W.inclusion e).val (W.new e)
    · intro e
      change (W.inclusion (W.map.rotation e)).val.val = _
      rw [W.rotation e]
      exact S.cancel_new_rotation d hd hdnegative (W.inclusion e).val (W.new e)
    · intro e
      rw [W.forward e, M.restrict_vertexWord p he hr]
      exact S.cancel_new_vertexWord d hd hdnegative (W.inclusion e).val (W.new e)
    · intro e
      rw [W.backward e, M.restrict_reverseVertexWord p he hr]
      exact S.cancel_new_reverseVertexWord d hd hdnegative (W.inclusion e).val (W.new e)
    · intro e
      exact W.value e
termination_by Fintype.card D
decreasing_by
  classical
  have hsub : Fintype.card E ≤ Fintype.card C.Dart := Fintype.card_subtype_le _
  exact lt_of_le_of_lt hsub C.card_darts_lt

end OldDiscSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
