module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionSystem

/-!
# Global erasure of old factor discs with all new occurrences retained

This finite surgery keeps every original new incidence and its coefficient and quotient
potential. Euler equality is preserved. No region equation is asserted during the erasure:
afterwards those equations can be recovered separately using embedded coefficient factors.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

universe u
variable {D : Type u} {X H Q : Type*} [Finite D] [Group H] [Group Q]
    {P : RibbonMap D} {L : RibbonLabelling P X H} {q : H →* Q}

/-- Global old-disc erasure with a bijection onto all original new incidences. -/
structure OldDiscErasure (S : OldDiscSystem L) (F : CornerPotential L q) where
  Dart : Type u
  [finite : Finite Dart]
  map : RibbonMap Dart
  label : RibbonLabelling map X H
  potential : CornerPotential label q
  inclusion : Dart ↪ D
  euler : map.EulerEquality
  new : ∀ d, ¬S.old (inclusion d)
  covers : ∀ d, ¬S.old d → ∃ e, inclusion e = d
  arc : ∀ d, label.arc d = L.arc (inclusion d)
  corner : ∀ d, label.corner d = L.corner (inclusion d)
  rotation : ∀ d, inclusion (map.rotation d) = P.rotation (inclusion d)
  value : ∀ d, potential.value d = F.value (inclusion d)

attribute [instance] OldDiscErasure.finite

namespace OldDiscErasure

variable {S : OldDiscSystem L} {F : CornerPotential L q} (W : OldDiscErasure S F)

/-- The surviving dart type is exactly the full set of original new incidences. -/
noncomputable def newEquiv : W.Dart ≃ {d // ¬S.old d} :=
  Equiv.ofBijective (fun d ↦ ⟨W.inclusion d, W.new d⟩) (by
    constructor
    · intro d e h
      exact W.inclusion.injective (congrArg Subtype.val h)
    · rintro ⟨d, hd⟩
      obtain ⟨e, he⟩ := W.covers d hd
      exact ⟨e, Subtype.ext he⟩)

end OldDiscErasure

namespace OldDiscSystem

/-- Normalize all old factor vertices, without discarding any new vertex or any component. -/
theorem exists_erasure (D : Type u) [Fintype D] (P : RibbonMap D)
    (L : RibbonLabelling P X H) (S : OldDiscSystem L) (F : CornerPotential L q)
    (hE : P.EulerEquality) : Nonempty (OldDiscErasure S F) := by
  classical
  by_cases hall : ∀ d, ¬S.old d
  · exact ⟨{
      Dart := D
      map := P
      label := L
      potential := F
      inclusion := Function.Embedding.refl D
      euler := hE
      new := hall
      covers := fun d _ ↦ ⟨d, rfl⟩
      arc := fun _ ↦ rfl
      corner := fun _ ↦ rfl
      rotation := fun _ ↦ rfl
      value := fun _ ↦ rfl }⟩
  · obtain ⟨a, ha⟩ := not_forall.mp hall
    have ha : S.old a := not_not.mp ha
    obtain ⟨d, had, hnegative⟩ := (S.disc a ha).exists_negative
    have hd : S.old d := (S.constant had).mp ha
    let C := S.cancellation d hd hnegative
    let harc := S.cancellation_arc d hd hnegative
    let hleft := S.cancellation_corner d hd hnegative
    let M := C.labelling L harc
    let T := S.cancel d hd hnegative
    let K := F.cancel C harc hleft
    obtain ⟨W⟩ := exists_erasure C.Dart C.delete M T K (C.delete_euler hE)
    refine ⟨{
      Dart := W.Dart
      map := W.map
      label := W.label
      potential := W.potential
      inclusion := W.inclusion.trans ⟨Subtype.val, Subtype.val_injective⟩
      euler := W.euler
      new := W.new
      covers := ?_
      arc := W.arc
      corner := ?_
      rotation := ?_
      value := W.value }⟩
    · intro e he
      let e' := S.survivingNew d hd hnegative e he
      obtain ⟨z, hz⟩ := W.covers e' he
      exact ⟨z, congrArg Subtype.val hz⟩
    · intro e
      rw [W.corner]
      exact S.cancel_new_corner d hd hnegative (W.inclusion e) (W.new e)
    · intro e
      change (W.inclusion (W.map.rotation e)).val = _
      rw [W.rotation]
      exact S.cancel_new_rotation d hd hnegative (W.inclusion e) (W.new e)
termination_by Fintype.card D
decreasing_by exact C.card_darts_lt

end OldDiscSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
