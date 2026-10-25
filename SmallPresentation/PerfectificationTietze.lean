module

public import SmallPresentation.PerfectificationData
public import SmallPresentation.ConversionPipeline

/-! # Exact elimination of the source factor in the perfectification -/
@[expose] public section

namespace SmallPresentationStatements.Conversion.Relative
open Word

variable {k μ : ℕ}

abbrev FreeProduct (T : FP k μ) := Monoid.CoprodI (FactorGroup T)

def freeVertex (T : FP k μ) (v : Fin 2) : FreeProduct T :=
  Monoid.CoprodI.of (i := .inr v) (Multiplicative.ofAdd 1)

def freeSource (T : FP k μ) : T.Group →* FreeProduct T :=
  Monoid.CoprodI.of (M := FactorGroup T) (i := .inl ())

theorem freeVertex_zpow (T : FP k μ) (v : Fin 2) (n : ℤ) :
    Monoid.CoprodI.of (M := FactorGroup T) (i := .inr v) (Multiplicative.ofAdd n) =
      freeVertex T v ^ n := by
  rw [freeVertex, ← map_zpow]
  congr 1
  simp [← ofAdd_zsmul]

private theorem block_product {H : Type*} [_root_.Group H] (x y : H) (es : List ℕ) :
    (List.ofFn fun p : Fin (2 * es.length) ↦
      if p.val % 2 = 0 then x else y ^ es[p.val / 2]' (by have hp := p.isLt; omega)).prod =
        (es.map fun e ↦ x * y ^ e).prod := by
  rw [List.ofFn_mul']
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ]
  simp only [Nat.add_zero, Nat.zero_add, Nat.mul_mod_right]
  have hm (i : Fin es.length) : (2 * i.val + 1) % 2 ≠ 0 := by omega
  have hd (i : Fin es.length) : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [hm, hd]
  rw [List.prod_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.prod_cons, List.prod_nil, mul_one]
  exact congrArg List.prod (List.ofFn_getElem_eq_map es (fun e ↦ x * y ^ e))

private theorem eval_blocks {H : Type*} [_root_.Group H] (x y : H) (es : List ℕ) :
    eval ![x,y] (blocks es) = (es.map fun e ↦ x * y ^ e).prod := by
  induction es with
  | nil => simp [blocks]
  | cons e es ih =>
    simp only [blocks, List.flatMap_cons, eval_append, eval_gen, eval_power,
      List.map_cons, List.prod_cons] at *
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_assoc] using
      congrArg (fun z ↦ (x * y ^ e) * z) ih

theorem relatorValue_literal (T : FP k μ) (i : Row k) :
    RelativeSmallCancellation.relatorValue (FactorGroup T) (rowLength T) (rows T) i =
      freeSource T (coefficient T i) * eval (freeVertex T) (blocks (markerList i)) := by
  classical
  have hv : freeVertex T = ![freeVertex T 0, freeVertex T 1] := by
    funext j; fin_cases j <;> rfl
  rw [hv, eval_blocks]
  have hr (p : Fin (rowLength T i)) :
      RelativeSmallCancellation.includeSyllable (FactorGroup T) (rows T i p) =
        if h : p.val < (special T i).toNat then freeSource T (coefficient T i)
        else if (p.val - (special T i).toNat) % 2 = 0 then freeVertex T 0
        else freeVertex T 1 ^ (markerList i)[(p.val - (special T i).toNat) / 2]'(by
          have hp := p.isLt; dsimp [rowLength] at hp; omega) := by
    unfold rows
    split
    · rfl
    · split
      · rfl
      · change Monoid.CoprodI.of (M := FactorGroup T) (i := .inr 1) _ = _
        rw [freeVertex_zpow, zpow_natCast]
        rfl
  unfold RelativeSmallCancellation.relatorValue
  simp_rw [hr]
  by_cases hs : special T i = false
  ·
    have hc : coefficient T i = 1 := by
      by_contra h
      have := (special_iff T i).mpr h
      simp [hs] at this
    simp only [rowLength, hs, Bool.toNat_false, Fin.val_cast, Nat.add_zero, Nat.not_lt_zero,
      ↓reduceDIte, Nat.sub_zero, hc, map_one, one_mul]
    exact block_product _ _ _
  · have ht : special T i = true := Bool.eq_true_of_not_eq_false hs
    simp only [rowLength, ht, Bool.toNat_true, Fin.val_cast]
    rw [List.ofFn_succ]
    have hlt (n : ℕ) : ¬n + 1 < 1 := by omega
    simp only [Fin.val_zero, Nat.zero_lt_one, ↓reduceDIte, List.prod_cons,
      Fin.val_succ, hlt, Nat.add_sub_cancel]
    rw [block_product]

noncomputable def projection (T : FP k μ) : FreeProduct T →* RelativeGroup T :=
  QuotientGroup.mk' (RelativeSmallCancellation.relatorSubgroup
    (FactorGroup T) (rowLength T) (rows T))

noncomputable def vertex (T : FP k μ) (j : Fin 2) : RelativeGroup T :=
  factorMap T (.inr j) (Multiplicative.ofAdd 1)

@[simp] theorem projection_freeVertex (T : FP k μ) (j : Fin 2) :
    projection T (freeVertex T j) = vertex T j := rfl

@[simp] theorem projection_freeSource (T : FP k μ) (x : T.Group) :
    projection T (freeSource T x) = factorMap T (.inl ()) x := rfl

theorem row_eq_one (T : FP k μ) (i : Row k) :
    factorMap T (.inl ()) (coefficient T i) *
      eval (vertex T) (blocks (markerList i)) = 1 := by
  have h : projection T
      (RelativeSmallCancellation.relatorValue (FactorGroup T) (rowLength T) (rows T) i) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩)
  rw [relatorValue_literal, map_mul, projection_freeSource, map_eval] at h
  simpa only [projection_freeVertex] using h

theorem source_generator_eq_code (T : FP k μ) (i : Fin k) :
    factorMap T (.inl ()) (PresentedGroup.of i) = eval (vertex T) (perfectCode i) := by
  have h := row_eq_one T (.inl i)
  change factorMap T (.inl ()) ((PresentedGroup.of i)⁻¹) * eval _ (perfectCode i) = 1 at h
  rw [map_inv] at h
  exact inv_mul_eq_one.mp h

theorem dummy_eq_one (T : FP k μ) (j : Fin 2) :
    eval (vertex T) (if j = 0 then dummy₁ else dummy₂) = 1 := by
  have h := row_eq_one T (.inr j)
  fin_cases j <;> simpa [coefficient, markerList, dummy₁, dummy₂] using h

noncomputable def perfectToRelative (T : FP k μ) :
    (perfectification T).Group →* RelativeGroup T :=
  presentationHom (perfectification T) (vertex T) (by
    intro j
    by_cases h : j.val < μ
    · simp only [perfectification, h, ↓reduceDIte, eval_subst]
      have hf : (fun i ↦ eval (vertex T) (perfectCode i)) =
          fun i ↦ factorMap T (.inl ()) (PresentedGroup.of i) := by
        funext i
        exact (source_generator_eq_code T i).symm
      rw [hf, ← map_eval, T.eval_relator, map_one]
    · by_cases hj : j.val = μ
      · simp only [perfectification, hj, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
        exact dummy_eq_one T 0
      · simp only [perfectification, h, hj, ↓reduceDIte, ↓reduceIte]
        exact dummy_eq_one T 1)

@[simp] theorem perfectToRelative_of (T : FP k μ) (j : Fin 2) :
    perfectToRelative T (PresentedGroup.of j) = vertex T j := presentationHom_of _ _ _ _

def factorsToPerfect (T : FP k μ) : ∀ a : Factor, FactorGroup T a →* (perfectification T).Group
  | .inl _ => perfectificationHom T
  | .inr j => zpowersHom _ (PresentedGroup.of j)

def freeToPerfect (T : FP k μ) : FreeProduct T →* (perfectification T).Group :=
  Monoid.CoprodI.lift (factorsToPerfect T)

@[simp] theorem freeToPerfect_freeVertex (T : FP k μ) (j : Fin 2) :
    freeToPerfect T (freeVertex T j) = PresentedGroup.of j := by
  simp [freeToPerfect, freeVertex, factorsToPerfect]

@[simp] theorem freeToPerfect_freeSource (T : FP k μ) (x : T.Group) :
    freeToPerfect T (freeSource T x) = perfectificationHom T x :=
  Monoid.CoprodI.lift_of _ _

theorem perfectification_dummy (T : FP k μ) (j : Fin 2) :
    eval (PresentedGroup.of (rels := (perfectification T).relSet))
      (if j = 0 then dummy₁ else dummy₂) = 1 := by
  have h := (perfectification T).eval_relator (Fin.natAdd μ j)
  fin_cases j <;> simpa [perfectification] using h

theorem freeToPerfect_kills_rows (T : FP k μ) (i : Row k) :
    freeToPerfect T
      (RelativeSmallCancellation.relatorValue (FactorGroup T) (rowLength T) (rows T) i) = 1 := by
  rw [relatorValue_literal, map_mul, freeToPerfect_freeSource, map_eval]
  simp only [freeToPerfect_freeVertex]
  cases i with
  | inl i =>
    simp only [coefficient, map_inv, perfectificationHom, presentationHom_of,
      markerList, perfectCode, inv_mul_cancel]
  | inr j =>
    have h := perfectification_dummy T j
    fin_cases j <;> simpa [coefficient, markerList, dummy₁, dummy₂] using h

noncomputable def relativeToPerfect (T : FP k μ) :
    RelativeGroup T →* (perfectification T).Group :=
  QuotientGroup.lift _ (freeToPerfect T) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact freeToPerfect_kills_rows T i)

@[simp] theorem relativeToPerfect_factor (T : FP k μ) (a : Factor) (x : FactorGroup T a) :
    relativeToPerfect T (factorMap T a x) = factorsToPerfect T a x :=
  Monoid.CoprodI.lift_of _ _

@[simp] theorem relativeToPerfect_vertex (T : FP k μ) (j : Fin 2) :
    relativeToPerfect T (vertex T j) = PresentedGroup.of j := by
  calc
    _ = factorsToPerfect T (.inr j) (Multiplicative.ofAdd 1) := relativeToPerfect_factor T _ _
    _ = PresentedGroup.of j := by simp [factorsToPerfect]

theorem perfectToRelative_left_inverse (T : FP k μ) :
    Function.LeftInverse (relativeToPerfect T) (perfectToRelative T) := by
  have h : (relativeToPerfect T).comp (perfectToRelative T) =
      MonoidHom.id (perfectification T).Group := by
    apply PresentedGroup.ext
    intro j
    simp
  exact DFunLike.congr_fun h

theorem perfectToRelative_source (T : FP k μ) :
    (perfectToRelative T).comp (perfectificationHom T) = factorMap T (.inl ()) := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, perfectificationHom, presentationHom_of,
    map_eval, perfectToRelative_of]
  exact (source_generator_eq_code T i).symm

private theorem cyclicHom_ext {H : Type*} [_root_.Group H]
    (f g : Multiplicative ℤ →* H) (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) :
    f = g := by
  apply MonoidHom.ext
  intro x
  have hx : (Multiplicative.ofAdd (1 : ℤ)) ^ x.toAdd = x := by simp [← ofAdd_zsmul]
  rw [← hx, map_zpow, map_zpow, h]

theorem perfectToRelative_right_inverse (T : FP k μ) :
    Function.RightInverse (relativeToPerfect T) (perfectToRelative T) := by
  have h : ((perfectToRelative T).comp (relativeToPerfect T)).comp (projection T) =
      projection T := by
    apply Monoid.CoprodI.ext_hom
    intro a
    cases a with
    | inl a =>
      cases a
      apply PresentedGroup.ext
      intro i
      change perfectToRelative T (relativeToPerfect T
        (factorMap T (.inl ()) (PresentedGroup.of i))) = factorMap T (.inl ()) (PresentedGroup.of i)
      rw [relativeToPerfect_factor]
      exact DFunLike.congr_fun (perfectToRelative_source T) (PresentedGroup.of i)
    | inr j =>
      apply cyclicHom_ext
      change perfectToRelative T (relativeToPerfect T (vertex T j)) = vertex T j
      rw [relativeToPerfect_vertex, perfectToRelative_of]
  intro x
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective
    (RelativeSmallCancellation.relatorSubgroup (FactorGroup T) (rowLength T) (rows T)) x
  change projection T w = x at hw
  rw [← hw]
  exact DFunLike.congr_fun h w

noncomputable def equivPerfectification (T : FP k μ) :
    RelativeGroup T ≃* (perfectification T).Group :=
  { relativeToPerfect T with
    invFun := perfectToRelative T
    left_inv := perfectToRelative_right_inverse T
    right_inv := perfectToRelative_left_inverse T }

end SmallPresentationStatements.Conversion.Relative
