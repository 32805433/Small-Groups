module

public import SmallPresentation.SmallCancellationDipoleRelativeFactorFaces

/-!
# Splitting inverse rows into old factor discs preserves every coefficient region

Changing only successors of negative markers leaves every positive face step unchanged.
Negative face corners are all one. Consequently the complete coefficient-region value at
every original incidence survives any alternating rotation with the same positive-marker
successors. This applies to splitting a merged inverse pair into four-marker factor discs;
it does not apply to splitting all markers into separate pairs.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling

open PermutationCycles

variable {D X H : Type*} [Group H] {P : RibbonMap D} (L : RibbonLabelling P X H)

omit [Group H] in
/-- An alternating marker labelling makes the face permutation preserve marker phase. -/
theorem face_phase (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2) (d : D) :
    (L.arc (P.face d)).2 = (L.arc d).2 := by
  have hh := halt (P.face d)
  rw [RibbonMap.face_apply, Equiv.apply_symm_apply] at hh
  have he := congrArg Prod.snd (L.edge_arc d)
  change (L.arc (P.edge d)).2 = !(L.arc d).2 at he
  rw [hh] at he
  change (L.arc (P.rotation.symm (P.edge d))).2 = _
  simpa only [Bool.not_not] using congrArg Bool.not he

/-- Every negative face has literally trivial coefficient product, independently of planarity. -/
theorem negative_faceValue [Finite D]
    (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2)
    (hneg : ∀ d, (L.arc d).2 = false → L.corner d = 1)
    (d : D) (hd : (L.arc d).2 = false) : L.faceValue d = 1 := by
  apply List.prod_eq_one
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  have hc : P.face.SameCycle d e := by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  have hp := constant_on_cycles P.face (fun a ↦ (L.arc a).2) (L.face_phase halt) hc
  rw [hneg e (hp.symm.trans hd), inv_one]

/-- Retain all original arc and corner labels while changing the vertex rotation. -/
def withRotation (τ : Equiv.Perm D) : RibbonLabelling (P.withRotation τ) X H where
  arc := L.arc
  corner := L.corner
  edge_arc := L.edge_arc

omit [Group H] in
/-- A permutation retaining all positive-marker successors automatically retains alternation. -/
theorem alternating_of_positive_successors (τ : Equiv.Perm D)
    (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2)
    (hpos : ∀ d, (L.arc d).2 = true → τ d = P.rotation d) (d : D) :
    (L.arc (τ d)).2 = !(L.arc d).2 := by
  cases hd : (L.arc d).2 with
  | true => rw [hpos d hd]; simpa only [hd] using halt d
  | false =>
    cases ht : (L.arc (τ d)).2 with
    | true => rfl
    | false =>
      let e := P.rotation.symm (τ d)
      have he : P.rotation e = τ d := P.rotation.apply_symm_apply _
      have hh := halt e
      rw [he, ht] at hh
      have hp : (L.arc e).2 = true := by
        cases hb : (L.arc e).2 with
        | false => simp only [hb, Bool.not_false, Bool.false_eq_true] at hh
        | true => rfl
      have htau := hpos e hp
      rw [he] at htau
      have hed := τ.injective htau
      rw [hed, hd] at hp
      contradiction

omit [Group H] in
/-- The inverse rotation at a positive face step is determined by positive-marker successors. -/
theorem positive_face_step (τ : Equiv.Perm D)
    (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2)
    (hpos : ∀ d, (L.arc d).2 = true → τ d = P.rotation d)
    (d : D) (hd : (L.arc d).2 = true) : (P.withRotation τ).face d = P.face d := by
  apply τ.injective
  change τ (τ.symm (P.edge d)) = τ (P.face d)
  rw [Equiv.apply_symm_apply, hpos _ ((L.face_phase halt d).trans hd),
    RibbonMap.face_apply, Equiv.apply_symm_apply]

omit [Group H] in
/-- Positive face boundaries retain their exact original ordered incidence lists. -/
theorem positive_faceBoundary [Finite D] (τ : Equiv.Perm D)
    (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2)
    (hpos : ∀ d, (L.arc d).2 = true → τ d = P.rotation d)
    (d : D) (hd : (L.arc d).2 = true) :
    (P.withRotation τ).faceBoundary d = P.faceBoundary d := by
  symm
  apply ((cycleBoundary_walk P.face d).changePerm ?_).eq_cycleBoundary
    (cycleBoundary_ne_nil P.face d) (cycleBoundary_nodup P.face d)
  intro e he
  have hc : P.face.SameCycle d e := by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  have hp := constant_on_cycles P.face (fun a ↦ (L.arc a).2) (L.face_phase halt) hc
  exact L.positive_face_step τ halt hpos e (hp.symm.trans hd)

/-- Splitting only at positive incoming markers preserves every original coefficient-region
value. Both noncommutativity and disconnected resulting pictures are allowed. -/
theorem withRotation_faceValue [Finite D] (τ : Equiv.Perm D)
    (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2)
    (hneg : ∀ d, (L.arc d).2 = false → L.corner d = 1)
    (halt' : ∀ d, (L.arc (τ d)).2 = !(L.arc d).2)
    (hpos : ∀ d, (L.arc d).2 = true → τ d = P.rotation d) (d : D) :
    (L.withRotation τ).faceValue d = L.faceValue d := by
  cases hd : (L.arc d).2 with
  | false =>
    rw [(L.withRotation τ).negative_faceValue halt' hneg d hd,
      L.negative_faceValue halt hneg d hd]
  | true =>
    change (((P.withRotation τ).faceBoundary d).map (fun e ↦ (L.corner e)⁻¹)).prod = _
    rw [L.positive_faceBoundary τ halt hpos d hd]
    rfl

/-- Positive-marker successor preservation alone determines all region equations. -/
theorem withRotation_faceValue_of_positive_successors [Finite D] (τ : Equiv.Perm D)
    (halt : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2)
    (hneg : ∀ d, (L.arc d).2 = false → L.corner d = 1)
    (hpos : ∀ d, (L.arc d).2 = true → τ d = P.rotation d) (d : D) :
    (L.withRotation τ).faceValue d = L.faceValue d :=
  L.withRotation_faceValue τ halt hneg (L.alternating_of_positive_successors τ halt hpos) hpos d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling
