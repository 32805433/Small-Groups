module

public import SmallPresentation.SignedRelative

/-! # Exact elimination of the auxiliary source-group factors -/
@[expose] public section

namespace SmallPresentationStatements.SignedCoding
namespace Relative
open Word

variable {L d : ℕ}

abbrev FreeProduct (Q : FP 2 L) := Monoid.CoprodI (FactorGroup Q (d := d))

def freeVertex (Q : FP 2 L) (v : Fin d) : FreeProduct Q (d := d) :=
  Monoid.CoprodI.of (i := .inr v) (Multiplicative.ofAdd 1)

def freeSource (Q : FP 2 L) (a : Pair d) : Q.Group →* FreeProduct Q (d := d) :=
  Monoid.CoprodI.of (M := FactorGroup Q) (i := .inl a)

theorem freeVertex_zpow (Q : FP 2 L) (v : Fin d) (n : ℤ) :
    (Monoid.CoprodI.of (M := FactorGroup Q) (i := .inr v) (Multiplicative.ofAdd n)) = freeVertex Q v ^ n := by
  rw [freeVertex, ← map_zpow]
  congr 1
  simp [← ofAdd_zsmul]

set_option maxRecDepth 10000 in
theorem rows_literal (Q : FP 2 L) (a : Pair d) (j : Fin 2) :
    List.ofFn (rows Q (a, j)) =
      ⟨.inl a, (PresentedGroup.of j)⁻¹⟩ :: (codePowers j).flatMap
        (fun q ↦ [⟨.inr a.val.1, Multiplicative.ofAdd 1⟩,
          ⟨.inr a.val.2, Multiplicative.ofAdd q⟩]) := by
  apply List.map_injective_iff.mpr (decode_injective Q)
  rw [List.map_ofFn]
  simp only [Function.comp_def]
  have hh : (fun p ↦ decode Q (rows Q (a, j) p)) =
      syllable (PresentedGroup.of (rels := Q.relSet)) a.val.1 a.val.2 j true := by
    funext p
    exact decode_oriented Q (a, j) true p
  rw [hh]
  change syllableRow _ _ _ _ true = _
  rw [syllableRow_literal]
  simp [List.map_flatMap, decode]

private theorem prod_blocks (Q : FP 2 L) (r u : Fin d) (es : List ℤ) :
    ((es.flatMap (fun q ↦
      [⟨.inr r, Multiplicative.ofAdd 1⟩, ⟨.inr u, Multiplicative.ofAdd q⟩])).map
        (RelativeSmallCancellation.includeSyllable (FactorGroup Q))).prod =
      (es.map fun q ↦ freeVertex Q r * freeVertex Q u ^ q).prod := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, ih,
      RelativeSmallCancellation.includeSyllable]
    rw [freeVertex_zpow Q r 1, freeVertex_zpow Q u e, zpow_one]

private theorem eval_natBlocks {H : Type*} [_root_.Group H] (x y : H) (es : List ℕ) :
    eval ![x, y] (es.flatMap fun q ↦ gen 0 ++ power (gen 1) q) =
      (es.map fun q ↦ x * y ^ q).prod := by
  induction es with
  | nil => simp
  | cons e es ih => simp [ih, mul_assoc]

theorem eval_codePowers {H : Type*} [_root_.Group H] (x y : H) (j : Fin 2) :
    eval ![x, y] (![code₁, code₂] j) = (codePowers j |>.map fun q ↦ x * y ^ q).prod := by
  fin_cases j <;>
    simp [code₁, code₂, codePowers, eval_natBlocks, List.map_map, Function.comp_def, zpow_neg]

/-- The generic free-product relator is the literal equation identifying the chosen
source generator with the signed code word. -/
theorem relatorValue_literal (Q : FP 2 L) (a : Pair d) (j : Fin 2) :
    RelativeSmallCancellation.relatorValue (FactorGroup Q) rowLength (rows Q) (a, j) =
      (freeSource Q a (PresentedGroup.of j))⁻¹ * eval (freeVertex Q) (codeWord a.val.1 a.val.2 j) := by
  unfold RelativeSmallCancellation.relatorValue
  change (List.ofFn (RelativeSmallCancellation.includeSyllable (FactorGroup Q) ∘
    rows Q (a, j))).prod = _
  rw [← List.map_ofFn, rows_literal]
  simp only [List.map_cons, List.prod_cons, RelativeSmallCancellation.includeSyllable, map_inv]
  rw [prod_blocks, eval_codeWord, eval_codePowers]
  rfl

def projection (Q : FP 2 L) : FreeProduct Q (d := d) →* Group Q (d := d) :=
  QuotientGroup.mk' (RelativeSmallCancellation.relatorSubgroup (FactorGroup Q) rowLength (rows Q))

def vertex (Q : FP 2 L) (v : Fin d) : Group Q (d := d) :=
  factorMap Q (.inr v) (Multiplicative.ofAdd 1)

@[simp] theorem projection_freeVertex (Q : FP 2 L) (v : Fin d) :
    projection Q (freeVertex Q v) = vertex Q v := rfl

@[simp] theorem projection_freeSource (Q : FP 2 L) (a : Pair d) (x : Q.Group) :
    projection Q (freeSource Q a x) = factorMap Q (.inl a) x := rfl

theorem source_generator_eq_code (Q : FP 2 L) (a : Pair d) (j : Fin 2) :
    factorMap Q (.inl a) (PresentedGroup.of j) =
      eval (vertex Q) (codeWord a.val.1 a.val.2 j) := by
  have h : projection Q
      (RelativeSmallCancellation.relatorValue (FactorGroup Q) rowLength (rows Q) (a, j)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨(a, j), rfl⟩)
  rw [relatorValue_literal, map_mul, map_inv, projection_freeSource, map_eval] at h
  simp only [projection_freeVertex] at h
  exact inv_mul_eq_one.mp h

def codedToRelative (Q : FP 2 L) : CodedGroup Q d →* Group Q (d := d) :=
  PresentedGroup.toGroup (f := vertex Q) (by
    rintro _ ⟨r, u, hru, i, rfl⟩
    change eval (vertex Q) (row Q r u i) = 1
    rw [row, eval_subst]
    have hh : (fun j ↦ eval (vertex Q) (codeWord r u j)) =
        fun j ↦ factorMap Q (.inl ⟨(r, u), hru⟩) (PresentedGroup.of j) := by
      funext j
      exact (source_generator_eq_code Q ⟨(r, u), hru⟩ j).symm
    rw [hh, ← map_eval, Q.eval_relator, map_one])

@[simp] theorem codedToRelative_of (Q : FP 2 L) (v : Fin d) :
    codedToRelative Q (PresentedGroup.of v) = vertex Q v := PresentedGroup.toGroup.of _

def factorsToCoded (Q : FP 2 L) : ∀ a : Factor d, FactorGroup Q a →* CodedGroup Q d
  | .inl a => sourceHom Q a.val.1 a.val.2 a.property
  | .inr v => zpowersHom _ (PresentedGroup.of v)

def freeToCoded (Q : FP 2 L) : FreeProduct Q (d := d) →* CodedGroup Q d :=
  Monoid.CoprodI.lift (factorsToCoded Q)

@[simp] theorem freeToCoded_freeVertex (Q : FP 2 L) (v : Fin d) :
    freeToCoded Q (freeVertex Q v) = PresentedGroup.of v := by
  simp [freeToCoded, freeVertex, factorsToCoded]

@[simp] theorem freeToCoded_freeSource (Q : FP 2 L) (a : Pair d) (x : Q.Group) :
    freeToCoded Q (freeSource Q a x) = sourceHom Q a.val.1 a.val.2 a.property x := by
  exact Monoid.CoprodI.lift_of _ _

theorem freeToCoded_kills_rows (Q : FP 2 L) (a : Row d) :
    freeToCoded Q (RelativeSmallCancellation.relatorValue (FactorGroup Q) rowLength (rows Q) a) = 1 := by
  rcases a with ⟨a, j⟩
  rw [relatorValue_literal, map_mul, map_inv, freeToCoded_freeSource, map_eval]
  simp only [sourceHom, PresentedGroup.toGroup.of, freeToCoded_freeVertex, inv_mul_cancel]

def relativeToCoded (Q : FP 2 L) : Group Q (d := d) →* CodedGroup Q d :=
  QuotientGroup.lift _ (freeToCoded Q) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a, rfl⟩
    exact freeToCoded_kills_rows Q a)

@[simp] theorem relativeToCoded_factor (Q : FP 2 L) (a : Factor d) (x : FactorGroup Q a) :
    relativeToCoded Q (factorMap Q a x) = factorsToCoded Q a x :=
  Monoid.CoprodI.lift_of _ _

@[simp] theorem relativeToCoded_vertex (Q : FP 2 L) (v : Fin d) :
    relativeToCoded Q (vertex Q v) = PresentedGroup.of v := by
  calc
    _ = factorsToCoded Q (.inr v) (Multiplicative.ofAdd 1) :=
      relativeToCoded_factor Q (.inr v) (Multiplicative.ofAdd 1)
    _ = PresentedGroup.of v := by simp [factorsToCoded]

theorem codedToRelative_left_inverse (Q : FP 2 L) :
    Function.LeftInverse (relativeToCoded Q (d := d)) (codedToRelative Q) := by
  have h : (relativeToCoded Q).comp (codedToRelative Q) = MonoidHom.id (CodedGroup Q d) := by
    apply PresentedGroup.ext
    intro i
    simp
  exact DFunLike.congr_fun h

theorem codedToRelative_source (Q : FP 2 L) (a : Pair d) :
    (codedToRelative Q).comp (sourceHom Q a.val.1 a.val.2 a.property) = factorMap Q (.inl a) := by
  apply PresentedGroup.ext
  intro j
  simp only [MonoidHom.comp_apply, sourceHom, PresentedGroup.toGroup.of, map_eval,
    codedToRelative_of]
  exact (source_generator_eq_code Q a j).symm

private theorem cyclicHom_ext {H : Type*} [_root_.Group H]
    (f g : Multiplicative ℤ →* H) (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) :
    f = g := by
  apply MonoidHom.ext
  intro x
  have hx : (Multiplicative.ofAdd (1 : ℤ)) ^ x.toAdd = x := by
    simp [← ofAdd_zsmul]
  rw [← hx, map_zpow, map_zpow, h]

theorem codedToRelative_right_inverse (Q : FP 2 L) :
    Function.RightInverse (relativeToCoded Q (d := d)) (codedToRelative Q) := by
  have h : ((codedToRelative Q).comp (relativeToCoded Q)).comp (projection Q (d := d)) =
      projection Q (d := d) := by
    apply Monoid.CoprodI.ext_hom
    intro a
    cases a with
    | inl a =>
      apply PresentedGroup.ext
      intro j
      change codedToRelative Q (relativeToCoded Q
        (factorMap Q (.inl a) (PresentedGroup.of j))) = factorMap Q (.inl a) (PresentedGroup.of j)
      rw [relativeToCoded_factor]
      exact DFunLike.congr_fun (codedToRelative_source Q a) (PresentedGroup.of j)
    | inr v =>
      apply cyclicHom_ext
      change codedToRelative Q (relativeToCoded Q (vertex Q v)) = vertex Q v
      rw [relativeToCoded_vertex, codedToRelative_of]
  intro x
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective
    (RelativeSmallCancellation.relatorSubgroup (FactorGroup Q) rowLength (rows Q)) x
  change projection Q w = x at hw
  rw [← hw]
  exact DFunLike.congr_fun h w

/-- Elimination of all auxiliary factor generators yields precisely the originally defined
signed-code quotient, with explicit inverse homomorphisms. -/
def equivCodedGroup (Q : FP 2 L) : Group Q (d := d) ≃* CodedGroup Q d :=
  { relativeToCoded Q with
    invFun := codedToRelative Q
    left_inv := codedToRelative_right_inverse Q
    right_inv := codedToRelative_left_inverse Q }

/-- The actual ordered-pair map in `B_d` is injective by the proved
generic free-product small-cancellation theorem. -/
theorem sourceHom_injective (Q : FP 2 L) (hQ : Noncyclic Q.Group)
    (r u : Fin d) (hru : r ≠ u) : Function.Injective (sourceHom Q r u hru) := by
  have hf := factorMap_injective Q hQ (.inl ⟨(r, u), hru⟩)
  rw [← codedToRelative_source Q ⟨(r, u), hru⟩] at hf
  exact fun x y h ↦ hf (congrArg (codedToRelative Q) h)

theorem codedGroup_torsionfree (Q : FP 2 L) (hQ : Noncyclic Q.Group)
    (hT : IsMulTorsionFree Q.Group) : IsMulTorsionFree (CodedGroup Q d) := by
  let : IsMulTorsionFree (Group Q (d := d)) := group_torsionfree Q hQ hT
  exact (codedToRelative_left_inverse Q).injective.isMulTorsionFree (codedToRelative Q)

end Relative
end SmallPresentationStatements.SignedCoding
