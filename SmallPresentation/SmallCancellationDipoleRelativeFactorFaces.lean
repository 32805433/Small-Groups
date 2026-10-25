module

public import SmallPresentation.SmallCancellationDipoleRelativeWeights
public import SmallPresentation.SmallCancellationGeometryRelativeCornerFaces

/-!
# Recovering coefficient-region equations from factor embeddings and quotient potentials

A corner potential makes the image of every complete region product trivial by telescoping.
For alternating marker ribbons, positive region corners lie in one coefficient factor and
negative region corners are all one. Injectivity on each factor therefore recovers all
region equations, including those on components created by surgery.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D Q : Type*} [Group Q] {σ : Equiv.Perm D}

/-- Multiplicative potentials telescope along an actual finite departure walk. -/
theorem Walk.potential_product (v w : D → Q) (hv : ∀ d, v (σ d) = v d * w d)
    {a b : D} {l : List D} (h : Walk σ a b l) : v b = v a * (l.map w).prod := by
  induction h with
  | nil => simp
  | cons a b l h ih =>
    rw [ih, hv, List.map_cons, List.prod_cons, mul_assoc]

/-- A potential on a permutation makes the product on every complete finite cycle one. -/
theorem cycleProduct_eq_one_of_potential [Finite D] (σ : Equiv.Perm D)
    (v w : D → Q) (hv : ∀ d, v (σ d) = v d * w d) (a : D) :
    cycleProduct σ w a = 1 := by
  have h := (cycleBoundary_walk σ a).potential_product v w hv
  apply mul_left_cancel (a := v a)
  exact h.symm.trans (mul_one _).symm

end SmallPresentationStatements.PermutationCycles

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace CornerPotential

variable {D X H Q : Type*} [Finite D] [Group H] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {q : H →* Q} (F : CornerPotential L q)

include F in
/-- Every complete region product is killed by the quotient map, independently of planarity. -/
theorem faceValue_map_one (d : D) : q (L.faceValue d) = 1 := by
  have h := PermutationCycles.cycleProduct_eq_one_of_potential P.face
    (fun a ↦ F.value (P.rotation a)) (fun a ↦ q ((L.corner a)⁻¹)) (fun a ↦ by
      rw [RibbonMap.face_apply, Equiv.apply_symm_apply, F.edge, F.rotation, map_inv,
        mul_inv_cancel_right]) d
  simpa only [RibbonLabelling.faceValue, RibbonMap.faceBoundary,
    PermutationCycles.cycleProduct, PermutationCycles.cycleBoundary,
    Equiv.Perm.coe_pow, map_list_prod, List.map_map, Function.comp_def] using h

include F in
/-- Injectivity on any subgroup containing a region product recovers its actual equation. -/
theorem faceValue_eq_one_of_subgroup (K : Subgroup H)
    (hinj : Function.Injective (q.comp K.subtype)) (d : D) (hd : L.faceValue d ∈ K) :
    L.faceValue d = 1 := by
  have hh : (q.comp K.subtype) ⟨L.faceValue d, hd⟩ = (q.comp K.subtype) 1 := by
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_one] using F.faceValue_map_one d
  exact congrArg Subtype.val (hinj hh)

end CornerPotential

namespace RibbonLabelling

variable {D A : Type*} (G : A → Type*) [∀ a, Group (G a)] {P : RibbonMap D}
    (L : RibbonLabelling P A (Monoid.CoprodI G))

/-- Local factor and phase conditions of alternating relative coefficient diagrams. -/
structure FactorCorners : Prop where
  alternating : ∀ d, (L.arc (P.rotation d)).2 = !(L.arc d).2
  positive_tag : ∀ d, (L.arc d).2 = true → (L.arc (P.rotation d)).1 = (L.arc d).1
  negative_one : ∀ d, (L.arc d).2 = false → L.corner d = 1
  coefficient : ∀ d, L.corner d ∈ (Monoid.CoprodI.of : G (L.arc d).1 →* Monoid.CoprodI G).range

def faceKey (d : D) : Option A := bif (L.arc d).2 then some (L.arc d).1 else none

namespace FactorCorners

variable {G L} (C : FactorCorners G L)
include C

/-- Positive face steps stay in the same factor, while negative face steps remain negative. -/
theorem face_key (d : D) : faceKey G L (P.face d) = faceKey G L d := by
  have he := L.edge_arc d
  have hr := C.alternating (P.face d)
  have hstep : P.rotation (P.face d) = P.edge d := by
    rw [RibbonMap.face_apply, Equiv.apply_symm_apply]
  rw [hstep] at hr
  have hb : (L.arc (P.face d)).2 = (L.arc d).2 := by
    have hh := congrArg Prod.snd he
    change (L.arc (P.edge d)).2 = !(L.arc d).2 at hh
    rw [hr] at hh
    simpa only [Bool.not_not] using congrArg Bool.not hh
  cases hd : (L.arc d).2 with
  | false => simp only [faceKey, hb, hd, Bool.cond_false]
  | true =>
    have hp : (L.arc (P.face d)).2 = true := hb.trans hd
    have ht := C.positive_tag (P.face d) hp
    rw [hstep] at ht
    have he' := congrArg Prod.fst he
    change (L.arc (P.edge d)).1 = (L.arc d).1 at he'
    simp only [faceKey, hb, hd, Bool.cond_true]
    exact congrArg some (ht.symm.trans he')

/-- Every corner of one actual region lies in the same original factor subgroup. -/
theorem face_corner_mem [Finite D] (d e : D) (h : P.face.SameCycle d e) :
    L.corner e ∈ (Monoid.CoprodI.of : G (L.arc d).1 →* Monoid.CoprodI G).range := by
  have hk : faceKey G L d = faceKey G L e :=
    PermutationCycles.constant_on_cycles P.face (faceKey G L) C.face_key h
  cases he : (L.arc e).2 with
  | false => rw [C.negative_one e he]; exact one_mem _
  | true =>
    cases hd : (L.arc d).2 with
    | false => simp only [faceKey, hd, he, Bool.cond_false, Bool.cond_true] at hk; contradiction
    | true =>
      have ht : (L.arc d).1 = (L.arc e).1 := by
        simpa only [faceKey, hd, he, Bool.cond_true, Option.some.injEq] using hk
      rw [ht]
      exact C.coefficient e

/-- The full noncommutative region product lies in its original factor subgroup. -/
theorem faceValue_mem [Finite D] (d : D) :
    L.faceValue d ∈ (Monoid.CoprodI.of : G (L.arc d).1 →* Monoid.CoprodI G).range := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  apply inv_mem
  apply C.face_corner_mem d e
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
  exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)

end FactorCorners
end RibbonLabelling

namespace CornerPotential

variable {D A Q : Type*} [Finite D] (G : A → Type*) [∀ a, Group (G a)] [Group Q]
    {P : RibbonMap D} {L : RibbonLabelling P A (Monoid.CoprodI G)}
    {q : Monoid.CoprodI G →* Q} (F : CornerPotential L q)

include F in
/-- Factor embeddings and actual quotient paths suffice to recover every coefficient-region
relation on an alternating relative ribbon; no outside-face equation is assumed. -/
theorem faceValue_of_injective_factors (C : RibbonLabelling.FactorCorners G L)
    (hinj : ∀ a, Function.Injective (q.comp (Monoid.CoprodI.of : G a →* Monoid.CoprodI G))) (d : D) :
    L.faceValue d = 1 := by
  obtain ⟨x, hx⟩ := C.faceValue_mem d
  have hq : (q.comp (Monoid.CoprodI.of : G (L.arc d).1 →* Monoid.CoprodI G)) x =
      (q.comp (Monoid.CoprodI.of : G (L.arc d).1 →* Monoid.CoprodI G)) 1 := by
    simpa only [MonoidHom.comp_apply, hx, map_one] using F.faceValue_map_one d
  rw [← hx, hinj _ hq, map_one]

end CornerPotential
end SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool) (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)

include hrotation in
/-- Literal augmented rows retain the phase and factor support needed to recover all regions. -/
theorem factorCorners :
    RibbonLabelling.FactorCorners G (labelling length G rows labels signs P hedge) := by
  constructor
  · rintro ⟨o, k, b⟩
    rw [hrotation]
    cases b <;> rfl
  · rintro ⟨o, k, b⟩ hb
    cases b
    · rw [hrotation]
      rfl
    · contradiction
  · rintro ⟨o, k, b⟩ hb
    cases b
    · contradiction
    · rfl
  · rintro ⟨o, k, b⟩
    cases b
    · exact ⟨(literalSyllable length G rows (labels o) (signs o) k).2, rfl⟩
    · exact one_mem _

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
