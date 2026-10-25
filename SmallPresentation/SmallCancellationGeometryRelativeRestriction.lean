module

public import SmallPresentation.SmallCancellationGeometryFactorDisc
public import SmallPresentation.SmallCancellationGeometryRelativeMetric

/-! Exact labels, readings and quotient paths on invariant subribbons. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

variable {D : Type*} [Finite D] (P : RibbonMap D) (p : D → Prop)
    (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d)

theorem restrict_vertexBoundary (d : {d // p d}) :
    ((P.restrict p he hr).vertexBoundary d).map Subtype.val = P.vertexBoundary d.val :=
  PermutationCycles.cycleBoundary_map_injective (P.restrict p he hr).rotation P.rotation
    Subtype.val Subtype.val_injective (fun _ ↦ rfl) d

theorem restrict_faceBoundary (d : {d // p d}) :
    ((P.restrict p he hr).faceBoundary d).map Subtype.val = P.faceBoundary d.val :=
  PermutationCycles.cycleBoundary_map_injective (P.restrict p he hr).face P.face
    Subtype.val Subtype.val_injective (fun _ ↦ rfl) d

theorem restrict_sameVertex_iff (d e : {d // p d}) :
    (P.restrict p he hr).rotation.SameCycle d e ↔ P.rotation.SameCycle d.val e.val := by
  rw [← (P.restrict p he hr).mem_vertexBoundary_iff, ← P.mem_vertexBoundary_iff,
    ← P.restrict_vertexBoundary p he hr d]
  exact (List.mem_map_of_injective Subtype.val_injective).symm

theorem restrict_sameFace_iff (d e : {d // p d}) :
    (P.restrict p he hr).face.SameCycle d e ↔ P.face.SameCycle d.val e.val := by
  rw [← (P.restrict p he hr).mem_faceBoundary_iff, ← P.mem_faceBoundary_iff,
    ← P.restrict_faceBoundary p he hr d]
  exact (List.mem_map_of_injective Subtype.val_injective).symm

end RibbonMap

namespace RibbonLabelling

variable {D X H : Type*} {P : RibbonMap D} (L : RibbonLabelling P X H)
    (p : D → Prop) (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d)

noncomputable def restrict : RibbonLabelling (P.restrict p he hr) X H where
  arc d := L.arc d.val
  corner d := L.corner d.val
  edge_arc d := L.edge_arc d.val

theorem restrict_vertexWord [Finite D] (d : {d // p d}) :
    (L.restrict p he hr).vertexWord d = L.vertexWord d.val := by
  rw [vertexWord, vertexWord, ← P.restrict_vertexBoundary p he hr, List.map_map]
  rfl

theorem restrict_reverseVertexWord [Finite D] [Group H] (d : {d // p d}) :
    (L.restrict p he hr).reverseVertexWord d = L.reverseVertexWord d.val := by
  have hp : Function.minimalPeriod (P.restrict p he hr).rotation d =
      Function.minimalPeriod P.rotation d.val := by
    simpa only [List.length_map, RibbonMap.vertexBoundary_length] using
      congrArg List.length (P.restrict_vertexBoundary p he hr d)
  have hv (k : ℕ) : (((P.restrict p he hr).rotation.symm)^[k] d).val =
      P.rotation.symm^[k] d.val := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change P.rotation.symm (((P.restrict p he hr).rotation.symm^[k] d).val) =
        P.rotation.symm^[k + 1] d.val
      rw [ih, Function.iterate_succ_apply']
  simp only [reverseVertexWord, hp]
  apply congrArg List.ofFn
  funext k
  change (reverseLetter (L.arc ((P.restrict p he hr).rotation.symm^[k.val] d).val),
      (L.corner ((P.restrict p he hr).rotation.symm^[k.val + 1] d).val)⁻¹) = _
  rw [hv, hv]

theorem restrict_faceValue [Finite D] [Group H] (d : {d // p d}) :
    (L.restrict p he hr).faceValue d = L.faceValue d.val := by
  rw [faceValue, faceValue, ← P.restrict_faceBoundary p he hr, List.map_map]
  rfl

theorem restrict_cyclicallyReduced [Group H] (hred : L.CyclicallyReduced) :
    (L.restrict p he hr).CyclicallyReduced := fun d hd ↦ hred d.val hd

theorem restrict_factorDisc [Finite D] [Group H] (d : {d // p d})
    (h : FactorDisc L d.val) : FactorDisc (L.restrict p he hr) d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e hd
    exact h.tag e.val ((P.restrict_sameVertex_iff p he hr d e).mp hd)
  · intro e hd
    exact h.alternating e.val ((P.restrict_sameVertex_iff p he hr d e).mp hd)
  · intro e hd hs
    exact h.negative e.val ((P.restrict_sameVertex_iff p he hr d e).mp hd) hs
  · have hh := congrArg (fun l : List D ↦ (l.map L.corner).prod)
      (P.restrict_vertexBoundary p he hr d)
    simp only [List.map_map] at hh
    exact hh.trans h.product

end RibbonLabelling

namespace CornerPotential

variable {D X H Q : Type*} [Group H] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {q : H →* Q} (F : CornerPotential L q)
    (p : D → Prop) (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d)

noncomputable def restrict : CornerPotential (L.restrict p he hr) q where
  value d := F.value d.val
  edge d := F.edge d.val
  rotation d := F.rotation d.val

end CornerPotential

namespace AugmentedReadings

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type*} [Finite D] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)}
    (Q : AugmentedReadings G length rows P L)
    (p : D → Prop) (he : ∀ d, p (P.edge d) ↔ p d) (hr : ∀ d, p (P.rotation d) ↔ p d)

noncomputable def restrict :
    AugmentedReadings G length rows (P.restrict p he hr) (L.restrict p he hr) where
  origin d := Q.origin d.val
  forward d hd := by
    rw [L.restrict_vertexWord p he hr]
    exact Q.forward d.val hd
  backward d hd := by
    rw [L.restrict_reverseVertexWord p he hr]
    exact Q.backward d.val hd

end AugmentedReadings
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
