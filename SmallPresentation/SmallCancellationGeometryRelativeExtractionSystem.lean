module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionData
public import SmallPresentation.SmallCancellationGeometryRadialBoundary

/-!
# Old-disc systems and their exact inherited local data

Old vertices are specified by a rotation-invariant predicate. The same predicate is
restricted along actual surgery inclusions and component inclusions. In particular,
old-only components satisfy their omitted outer equation by the noncommutative radial
boundary theorem.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}

/-- The old vertices of a relative picture, with their actual factor-disc equations. -/
structure OldDiscSystem (L : RibbonLabelling P X H) where
  old : D → Prop
  invariant : ∀ d, old (P.rotation d) ↔ old d
  disc : ∀ d, old d → FactorDisc L d

namespace OldDiscSystem

variable {L : RibbonLabelling P X H} (S : OldDiscSystem L)

theorem constant {d e : D} (h : P.rotation.SameCycle d e) : S.old d ↔ S.old e :=
  P.vertex_predicate_constant S.old S.invariant h

/-- An old negative marker determines a genuine local cancellation. -/
def cancellation (d : D) (hd : S.old d) (hs : (L.arc d).2 = false) :
    AdjacentCancellation P := (S.disc d hd).cancellation d (.refl _ _) hs

omit [Finite D] in
theorem cancellation_arc (d : D) (hd : S.old d) (hs : (L.arc d).2 = false) :
    L.arc (S.cancellation d hd hs).right =
      reverseLetter (L.arc (S.cancellation d hd hs).left) :=
  (S.disc d hd).cancellation_arc d (.refl _ _) hs

omit [Finite D] in
theorem cancellation_corner (d : D) (hd : S.old d) (hs : (L.arc d).2 = false) :
    L.corner (S.cancellation d hd hs).left = 1 :=
  (S.disc d hd).cancellation_corner d (.refl _ _) hs

/-- Every surviving old vertex retains its exact factor-disc normal form. -/
noncomputable def cancel (d : D) (hd : S.old d) (hs : (L.arc d).2 = false) :
    OldDiscSystem ((S.cancellation d hd hs).labelling L (S.cancellation_arc d hd hs)) where
  old e := S.old e.val
  invariant := (S.cancellation d hd hs).retained_old_invariant S.old S.invariant
  disc e he := by
    by_cases h : P.rotation.SameCycle d e.val
    · exact (S.disc d hd).cancel d (.refl _ _) hs e h
    · exact (S.cancellation d hd hs).factorDisc_other L (S.cancellation_arc d hd hs)
        e h (S.disc e.val he) (S.cancellation_corner d hd hs)

/-- A new incidence cannot lie on the old vertex where cancellation occurs. -/
theorem new_other_vertex (d : D) (hd : S.old d) (e : D) (he : ¬ S.old e) :
    ¬ P.rotation.SameCycle d e := fun h ↦ he ((S.constant h).mp hd)

theorem cancel_new_vertexWord (d : D) (hd : S.old d) (hs : (L.arc d).2 = false)
    (e : (S.cancellation d hd hs).Dart) (he : ¬ S.old e.val) :
    ((S.cancellation d hd hs).labelling L (S.cancellation_arc d hd hs)).vertexWord e =
      L.vertexWord e.val :=
  (S.cancellation d hd hs).vertexWord_unchanged L (S.cancellation_arc d hd hs)
    e (S.new_other_vertex d hd e.val he)

theorem cancel_new_reverseVertexWord (d : D) (hd : S.old d) (hs : (L.arc d).2 = false)
    (e : (S.cancellation d hd hs).Dart) (he : ¬ S.old e.val) :
    ((S.cancellation d hd hs).labelling L (S.cancellation_arc d hd hs)).reverseVertexWord e =
      L.reverseVertexWord e.val :=
  (S.cancellation d hd hs).reverseVertexWord_unchanged L (S.cancellation_arc d hd hs)
    e (S.new_other_vertex d hd e.val he)

omit [Finite D] in
/-- The cyclic successor at every new vertex is the original successor. -/
theorem cancel_new_rotation (d : D) (hd : S.old d) (hs : (L.arc d).2 = false)
    (e : (S.cancellation d hd hs).Dart) (he : ¬S.old e.val) :
    ((S.cancellation d hd hs).delete.rotation e).val = P.rotation e.val := by
  classical
  rw [(S.cancellation d hd hs).rotation_val]
  apply ite_eq_right
  intro h
  exact he ((S.invariant e.val).mp (h.symm ▸ hd))

omit [Finite D] in
/-- New corner coefficients themselves remain unchanged, not just their cyclic products. -/
theorem cancel_new_corner (d : D) (hd : S.old d) (hs : (L.arc d).2 = false)
    (e : (S.cancellation d hd hs).Dart) (he : ¬S.old e.val) :
    ((S.cancellation d hd hs).labelling L (S.cancellation_arc d hd hs)).corner e =
      L.corner e.val := by
  apply (S.cancellation d hd hs).labelling_corner_of_ne L (S.cancellation_arc d hd hs)
  intro h
  exact he ((S.invariant e.val).mp (h.symm ▸ hd))

/-- Every original new incidence survives an old-disc cancellation. -/
def survivingNew (d : D) (hd : S.old d) (hs : (L.arc d).2 = false)
    (e : D) (he : ¬ S.old e) : (S.cancellation d hd hs).Dart :=
  ⟨e, by
    constructor
    · intro hh
      exact he (hh ▸ hd)
    · intro hh
      have hr : S.old (P.rotation d) := (S.invariant d).mpr hd
      exact he (hh ▸ hr)⟩

/-- Restriction to any invariant union of actual components retains all old-disc data. -/
noncomputable def restrict (p : D → Prop)
    (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d) :
    OldDiscSystem (L.restrict p he hr) where
  old d := S.old d.val
  invariant d := S.invariant d.val
  disc d hd := L.restrict_factorDisc p he hr d (S.disc d.val hd)

/-- The exceptional face of an old-only connected spherical picture is forced to be valid. -/
theorem outside_eq_one [Fintype D] (hall : ∀ d, S.old d)
    (hc : P.Connected) (hE : P.EulerEquality) (outside : D)
    (hfaces : ∀ d, ¬ P.face.SameCycle outside d → L.faceValue d = 1) :
    L.faceValue outside = 1 := by
  exact P.outside_corner_product_one L.corner hc hE outside
    (fun d ↦ (S.disc d (hall d)).product) hfaces

/-- An old-only component cannot carry a single defective region. This formulation uses
actual original incidence membership, making it suitable for a split cancellation. -/
theorem component_outside_eq_one [Fintype D] (outside : D)
    (hall : ∀ d, P.SameComponent outside d → S.old d)
    (hE : P.EulerEquality)
    (hfaces : ∀ d, P.SameComponent outside d →
      ¬ P.face.SameCycle outside d → L.faceValue d = 1) :
    L.faceValue outside = 1 := by
  classical
  let p := P.SameComponent outside
  let he := P.component_membership_edge outside
  let hr := P.component_membership_rotation outside
  let a : {d // p d} := ⟨outside, Relation.EqvGen.refl _⟩
  have hc : (P.restrict p he hr).Connected := P.componentRibbon_connected outside
  have hEuler : (P.restrict p he hr).EulerEquality :=
    P.restrict_euler p he hr hE
  have hh := (S.restrict p he hr).outside_eq_one
    (fun d ↦ hall d.val d.property) hc hEuler a (fun d hd ↦ ?_)
  · exact (L.restrict_faceValue p he hr a).symm.trans hh
  · rw [L.restrict_faceValue p he hr d]
    apply hfaces d.val d.property
    intro hf
    exact hd ((P.restrict_sameFace_iff p he hr a d).mpr hf)

end OldDiscSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
