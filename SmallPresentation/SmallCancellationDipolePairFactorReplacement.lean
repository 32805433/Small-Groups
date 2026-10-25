module

public import SmallPresentation.SmallCancellationDipolePairFactorReadings
public import SmallPresentation.SmallCancellationGeometryFactorReclassification
public import SmallPresentation.SmallCancellationGeometryEmbeddedRefinement
public import SmallPresentation.SmallCancellationDipoleRelativeFactorSplice

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks
open PermutationCycles

abbrev source (n : ℕ) : Equiv.Perm (Dart n) :=
  doublePerm (Equiv.sumCongr (finRotate n) (finRotate n))

noncomputable def splicedSource {n : ℕ} (k : Fin n) : Equiv.Perm (Dart n) :=
  cutAt (source n) (.inl k, true) (.inr k.rev, true)

/-- Actual local data for a matched inverse pair inside an arbitrary mixed diagram. -/
structure ReplacementData {D X H : Type*} [Group H] (P : RibbonMap D)
    (L : RibbonLabelling P X H) (n : ℕ) where
  anchor : Fin n
  embedding : Dart n ↪ D
  rotation : ∀ d, P.rotation (embedding d) = embedding (source n d)
  edge : P.edge (embedding (.inl anchor, false)) = embedding (.inr anchor.rev, true)
  tag : Fin n → X
  coeff : Fin n → H
  arc : ∀ d, L.arc (embedding d) = PairFactorBlocks.arc tag d
  corner : ∀ d, L.corner (embedding d) = rawCoefficient coeff d

namespace ReplacementData
variable {D X H : Type*} [Group H] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {n : ℕ} (T : ReplacementData P L n)

def point : D := T.embedding (.inl T.anchor, false)

theorem point_positive : (L.arc T.point).2 = true :=
  congrArg Prod.snd (T.arc (.inl T.anchor, false))

theorem face_point : T.embedding (.inr T.anchor.rev, false) = P.face T.point := by
  apply P.rotation.injective
  rw [T.rotation, RibbonMap.face_apply, Equiv.apply_symm_apply]
  exact T.edge.symm

theorem splice_rotation (d : Dart n) :
    (P.edgeSplice T.point).rotation (T.embedding d) =
      T.embedding (splicedSource T.anchor d) := by
  classical
  change cutAt P.rotation (P.rotation T.point) (P.edge T.point) (T.embedding d) = _
  rw [show P.rotation T.point = T.embedding (.inl T.anchor, true) from T.rotation _, show P.edge T.point = _ from T.edge]
  simp only [cutAt_apply, T.rotation, splicedSource]
  simp only [Equiv.swap_apply_def, T.embedding.injective.eq_iff]
  split_ifs <;> rfl

noncomputable def finalRotation : Equiv.Perm D :=
  replaceAlong (P.edgeSplice T.point).rotation (splicedSource T.anchor)
    (pairFactorRotation T.anchor) T.embedding

noncomputable def map : RibbonMap D := (P.edgeSplice T.point).withRotation T.finalRotation
noncomputable def labels : RibbonLabelling T.map X H :=
  (P.edgeSpliceLabelling L T.point).withRotation T.finalRotation

theorem final_rotation (d : Dart n) :
    T.map.rotation (T.embedding d) = T.embedding (pairFactorRotation T.anchor d) :=
  replaceAlong_apply _ _ _ _ T.splice_rotation d

theorem final_corner (d : Dart n) :
    T.labels.corner (T.embedding d) = coefficient T.anchor T.coeff d :=
  splice_corner L T.point T.anchor T.coeff T.embedding rfl T.face_point T.corner d

theorem final_arc (d : Dart n) : T.labels.arc (T.embedding d) = PairFactorBlocks.arc T.tag d := T.arc d

/-- Every resulting selected vertex is a proved old factor relation. -/
theorem factorDisc [Finite D] (d : Dart n) : FactorDisc T.labels (T.embedding d) :=
  factorDisc_of_embedding T.anchor T.tag T.coeff T.map T.labels T.embedding
    T.final_rotation T.final_arc T.final_corner d

theorem source_positive (d : Fin n ⊕ Fin n) :
    pairFactorRotation T.anchor (d, false) = splicedSource T.anchor (d, false) := by
  classical
  rcases d with k | k
  · simp [pairFactorRotation_apply, next, splicedSource, cutAt_apply, doublePerm_false,
      source, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · have hk : k = T.anchor.rev ↔ k.rev = T.anchor := by
      constructor <;> intro h <;> simpa using congrArg Fin.rev h
    simp [pairFactorRotation_apply, next, splicedSource, cutAt_apply, doublePerm_false,
      source, Equiv.swap_apply_def, hk]
    split_ifs <;> simp_all

/-- Positive successors agree with the actual anchor splice everywhere. -/
theorem positive_successors (d : D) (hd : (L.arc d).2 = true) :
    T.finalRotation d = (P.edgeSplice T.point).rotation d := by
  classical
  by_cases hm : d ∈ Set.range T.embedding
  · obtain ⟨⟨k, b⟩, rfl⟩ := hm
    have hs := congrArg Prod.snd (T.arc (k, b))
    cases b
    · rw [show T.finalRotation (T.embedding (k, false)) = _ from T.final_rotation _, T.source_positive,
        T.splice_rotation]
    · change (L.arc (T.embedding (k, true))).2 = false at hs
      rw [hs] at hd
      contradiction
  · exact replaceAlong_outside _ _ _ _ T.splice_rotation hm

/-- Every untouched original corner retains its original coefficient. -/
theorem corner_outside (d : D) (hd : d ∉ Set.range T.embedding) :
    T.labels.corner d = L.corner d := by
  classical
  have ha : d ≠ T.point := fun h ↦ hd ⟨(.inl T.anchor, false), h.symm⟩
  have hp : d ≠ P.face T.point := fun h ↦ hd ⟨(.inr T.anchor.rev, false), T.face_point.trans h.symm⟩
  change (if d = T.point then 1 else L.corner d * if d = P.face T.point then L.corner T.point else 1) = _
  rw [ite_eq_right ha, ite_eq_right hp, mul_one]

theorem rotation_outside (d : D) (hd : d ∉ Set.range T.embedding) :
    T.map.rotation d = P.rotation d := by
  rw [show T.map.rotation d = (P.edgeSplice T.point).rotation d from
    replaceAlong_outside _ _ _ _ T.splice_rotation hd]
  classical
  change Equiv.swap (P.rotation T.point) (P.edge T.point) (P.rotation d) = _
  have hn := invariant_complement P.rotation (source n) T.embedding T.rotation hd
  have ha : P.rotation d ≠ P.rotation T.point := by
    intro h
    exact hd ⟨(.inl T.anchor, false), (P.rotation.injective h).symm⟩
  have hb : P.rotation d ≠ P.edge T.point := fun h ↦
    hn ⟨(.inr T.anchor.rev, true), T.edge.symm.trans h.symm⟩
  exact Equiv.swap_apply_of_ne_of_ne ha hb

theorem selected_invariant (σ : Equiv.Perm D) (τ : Equiv.Perm (Dart n))
    (hσ : ∀ d, σ (T.embedding d) = T.embedding (τ d)) (d : D) :
    σ d ∈ Set.range T.embedding ↔ d ∈ Set.range T.embedding := by
  constructor
  · intro h
    by_contra hd
    exact invariant_complement σ τ T.embedding hσ hd h
  · rintro ⟨k, rfl⟩
    exact ⟨τ k, (hσ k).symm⟩

/-- All selected pair vertices become old discs and every preexisting old disc survives. -/
noncomputable def oldDiscs [Finite D] (S : OldDiscSystem L) : OldDiscSystem T.labels :=
  S.reclassify (Set.range T.embedding)
    (T.selected_invariant P.rotation (source n) T.rotation)
    (T.selected_invariant T.map.rotation (pairFactorRotation T.anchor) T.final_rotation)
    T.rotation_outside (fun _ _ ↦ rfl) T.corner_outside
    (fun d hd ↦ by obtain ⟨k, rfl⟩ := hd; exact T.factorDisc k)

/-- The surgery is an actual anchor merge followed by actual finite vertex splits. -/
theorem euler [Fintype D] (hE : P.EulerEquality)
    (hn : ¬P.rotation.SameCycle T.point (P.edge T.point)) : T.map.EulerEquality := by
  have hs := (pairFactorRotation_refinement T.anchor).toSplitRefinement.replaceAlong
    (P.edgeSplice T.point).rotation T.embedding T.splice_rotation
  exact (P.edgeSplice T.point).splitRefinement_preserves_euler hs
    ((P.edgeSplice_euler_iff T.point hn).mpr hE)

/-- No coefficient-region equation is lost: the only merge transfers its anchor
coefficient exactly, and subsequent positive-target cuts retain all positive faces. -/
theorem all_faces [Finite D]
    (hfaces : ∀ d, L.faceValue d = 1)
    (halt' : ∀ d, (L.arc ((P.edgeSplice T.point).rotation d)).2 = !(L.arc d).2)
    (hneg' : ∀ d, (L.arc d).2 = false → (P.edgeSpliceLabelling L T.point).corner d = 1)
    (hn : P.face T.point ≠ T.point) (d : D) : T.labels.faceValue d = 1 := by
  rw [show T.labels.faceValue d = (P.edgeSpliceLabelling L T.point).faceValue d from
    (P.edgeSpliceLabelling L T.point).withRotation_faceValue_of_positive_successors
      T.finalRotation halt' hneg' T.positive_successors d]
  exact P.edgeSplice_all_faces L T.point hn hfaces d

variable {A : Type*} {G : A → Type*} [∀ a, Group (G a)] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)} {n : ℕ}
    (T : ReplacementData P L n)

theorem factorCorners (C : RibbonLabelling.FactorCorners G L) :
    RibbonLabelling.FactorCorners G T.labels :=
  (C.edgeSplice T.point T.point_positive).withRotation T.finalRotation T.positive_successors

/-- Full noncircular face preservation for the actual inverse-pair-to-old-discs surgery. -/
theorem faces [Finite D] (C : RibbonLabelling.FactorCorners G L)
    (hfaces : ∀ d, L.faceValue d = 1)
    (hn : ¬P.rotation.SameCycle T.point (P.edge T.point)) :
    ∀ d, T.labels.faceValue d = 1 := by
  apply T.all_faces hfaces
    (C.edgeSplice T.point T.point_positive).alternating
    (C.edgeSplice T.point T.point_positive).negative_one
  intro h
  apply hn
  rw [← show P.rotation (P.face T.point) = P.edge T.point by
    rw [RibbonMap.face_apply, Equiv.apply_symm_apply], h]
  exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

end ReplacementData
end SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks
