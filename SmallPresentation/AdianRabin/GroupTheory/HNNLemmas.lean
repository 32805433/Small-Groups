module

/-
Ported from `GroupUndecidability/GroupTheory/HNNLemmas.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.UniversalGroup.Foundations.HNN.NormalForms

@[expose] public section

open Set

namespace UniversalGroup.HNNLemmas

variable {G : Type*} [Group G]
variable {A B : Subgroup G} {phi : A ≃* B}

/-- The stable letter conjugated by an element of the base group. -/
def conjugatedStable (C : Subgroup G) (P : G) : CentralizerHNN G C :=
  centralizerOf C P⁻¹ * centralizerStable C * centralizerOf C P

/-! Auxiliary restricted HNN extension for the calculation in
Lemma B.4 of the paper. -/

def conjugatePullback (A C : Subgroup G) (P : G) : Subgroup A :=
  C.comap ((MulAut.conj P).toMonoidHom.comp A.subtype)

def conjugatedEmbedding (A C : Subgroup G) (P : G) :
    CentralizerHNN A (conjugatePullback A C P) →* CentralizerHNN G C :=
  HNNExtension.lift
    ((centralizerOf C).comp A.subtype) (conjugatedStable C P) (by
      intro a
      let c : C := ⟨P * ((a : conjugatePullback A C P) : A) * P⁻¹, a.property⟩
      have hc : (centralizerOf C (c : G)) * centralizerStable C =
          centralizerStable C * centralizerOf C (c : G) := by
        simpa [centralizerOf, centralizerStable] using
          HNNExtension.of_mul_t (φ := MulEquiv.refl C) c
      let aG : G := (((a : conjugatePullback A C P) : A) : G)
      change
        (centralizerOf C P⁻¹ * centralizerStable C * centralizerOf C P) *
            centralizerOf C aG =
          centralizerOf C aG *
            (centralizerOf C P⁻¹ * centralizerStable C * centralizerOf C P)
      have hPa : P * aG = (c : G) * P := by
        dsimp [aG, c]
        simp
      have hPinvc : P⁻¹ * (c : G) = aG * P⁻¹ := by
        dsimp [aG, c]
        simp [mul_assoc]
      calc
        _ = centralizerOf C P⁻¹ * centralizerStable C *
              (centralizerOf C P * centralizerOf C aG) := by simp [mul_assoc]
        _ = centralizerOf C P⁻¹ * centralizerStable C *
              centralizerOf C (P * aG) := by
                rw [map_mul (centralizerOf C) P aG]
        _ = centralizerOf C P⁻¹ * centralizerStable C *
              centralizerOf C ((c : G) * P) := by rw [hPa]
        _ = centralizerOf C P⁻¹ * centralizerStable C *
              (centralizerOf C (c : G) * centralizerOf C P) := by
                rw [map_mul (centralizerOf C) (c : G) P]
        _ = centralizerOf C P⁻¹ *
              (centralizerStable C * centralizerOf C (c : G)) *
                centralizerOf C P := by simp [mul_assoc]
        _ = centralizerOf C P⁻¹ *
              (centralizerOf C (c : G) * centralizerStable C) *
                centralizerOf C P := by rw [hc]
        _ = (centralizerOf C P⁻¹ * centralizerOf C (c : G)) *
              centralizerStable C * centralizerOf C P := by simp [mul_assoc]
        _ = centralizerOf C (P⁻¹ * (c : G)) *
              centralizerStable C * centralizerOf C P := by
                rw [map_mul (centralizerOf C) P⁻¹ (c : G)]
        _ = centralizerOf C (aG * P⁻¹) *
              centralizerStable C * centralizerOf C P := by rw [hPinvc]
        _ = (centralizerOf C aG * centralizerOf C P⁻¹) *
              centralizerStable C * centralizerOf C P := by
                rw [map_mul (centralizerOf C) aG P⁻¹]
        _ = centralizerOf C aG *
              (centralizerOf C P⁻¹ * centralizerStable C *
                centralizerOf C P) := by simp [mul_assoc])

@[simp]
theorem conjugatedEmbedding_of (A C : Subgroup G) (P : G) (a : A) :
    conjugatedEmbedding A C P (HNNExtension.of a) = centralizerOf C (a : G) := by
  simp [conjugatedEmbedding]

@[simp]
theorem conjugatedEmbedding_t (A C : Subgroup G) (P : G) :
    conjugatedEmbedding A C P HNNExtension.t = conjugatedStable C P := by
  simp [conjugatedEmbedding]

theorem conjugatedEmbedding_range (A C : Subgroup G) (P : G) :
    MonoidHom.range (conjugatedEmbedding A C P) =
      generatedWith (A.map (centralizerOf C)) (conjugatedStable C P) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using HNNExtension.induction_on with
    | of a =>
        apply Subgroup.subset_closure
        exact Or.inl ⟨a, a.property, by simp⟩
    | t =>
        apply Subgroup.subset_closure
        exact Or.inr (Set.mem_singleton _)
    | mul x y hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x hx => simpa using Subgroup.inv_mem _ hx
  · unfold generatedWith
    rw [Subgroup.closure_le]
    rintro x (hx | rfl)
    · rcases hx with ⟨a, ha, rfl⟩
      exact ⟨HNNExtension.of (⟨a, ha⟩ : A), by simp⟩
    · exact ⟨HNNExtension.t, by simp⟩

theorem centralizer_generatedWith_reducedWord
    (C D : Subgroup G) {x : CentralizerHNN G C}
    (hx : x ∈ generatedWith (D.map (centralizerOf C)) (centralizerStable C)) :
    ∃ w : HNNExtension.NormalWord.ReducedWord G C C,
      w.prod (MulEquiv.refl C) = x ∧ w.head ∈ D ∧
        ∀ p ∈ w.toList, p.2 ∈ D := by
  have hphi : ∀ c : C,
      (c : G) ∈ D ↔ ((MulEquiv.refl C) c : G) ∈ D := by simp
  apply exists_reducedWord_of_mem_generatedWithStable D hphi
  simpa [generatedWith, generatedWithStable, centralizerOf, centralizerStable]
    using hx

def conjugatedList (P : G) : List (ℤˣ × A) → List (ℤˣ × G)
  | [] => []
  | [x] => [(x.1, P * (x.2 : G))]
  | x :: y :: xs =>
      (x.1, P * (x.2 : G) * P⁻¹) :: conjugatedList P (y :: xs)

lemma conjugatedStable_zpow_unit (C : Subgroup G) (P : G) (u : ℤˣ) :
    conjugatedStable C P ^ (u : ℤ) =
      centralizerOf C P⁻¹ * centralizerStable C ^ (u : ℤ) *
        centralizerOf C P := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp [conjugatedStable, mul_assoc]

lemma conjugatedList_prod (A C : Subgroup G) (P : G)
    (l : List (ℤˣ × A)) (hl : l ≠ []) :
    ((conjugatedList P l).map
        (fun p => centralizerStable C ^ (p.1 : ℤ) * centralizerOf C p.2)).prod =
      centralizerOf C P * conjugatedEmbedding A C P
        ((l.map (fun p => HNNExtension.t ^ (p.1 : ℤ) * HNNExtension.of p.2)).prod) := by
  induction l with
  | nil => simp at hl
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [conjugatedList, conjugatedEmbedding, conjugatedStable_zpow_unit,
            map_mul, mul_assoc]
      | cons y ys =>
          have htail : y :: ys ≠ [] := by simp
          simp only [conjugatedList, List.map_cons, List.prod_cons]
          rw [ih htail]
          simp [conjugatedEmbedding, conjugatedStable_zpow_unit, map_mul, mul_assoc]

lemma conjugated_toSubgroup_self {E : Type*} [Group E]
    (K : Subgroup E) (u : ℤˣ) :
    HNNExtension.toSubgroup K K u = K := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

lemma conjugatedList_chain (A C : Subgroup G) (P : G)
    (l : List (ℤˣ × A))
    (hchain : l.IsChain (fun a b =>
      a.2 ∈ HNNExtension.toSubgroup (conjugatePullback A C P)
        (conjugatePullback A C P) a.1 → a.1 = b.1)) :
    (conjugatedList P l).IsChain (fun a b =>
      a.2 ∈ HNNExtension.toSubgroup C C a.1 → a.1 = b.1) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x xs ih =>
      cases xs with
      | nil =>
          change [(x.1, P * (x.2 : G))].IsChain (fun a b =>
            a.2 ∈ HNNExtension.toSubgroup C C a.1 → a.1 = b.1)
          exact List.isChain_singleton _
      | cons y ys =>
          apply List.IsChain.cons
          · exact ih (List.isChain_cons.1 hchain).2
          · intro z hz hmem
            have hzfst : z.1 = y.1 := by
              cases ys <;> simp [conjugatedList] at hz
              · exact (congrArg Prod.fst hz).symm
              · exact (congrArg Prod.fst hz).symm
            have hxmem : x.2 ∈ conjugatePullback A C P := by
              change P * (x.2 : G) * P⁻¹ ∈ C
              rw [← conjugated_toSubgroup_self C x.1]
              exact hmem
            have hxmem' : x.2 ∈ HNNExtension.toSubgroup
                (conjugatePullback A C P) (conjugatePullback A C P) x.1 := by
              simpa [conjugated_toSubgroup_self] using hxmem
            have hxy := (List.isChain_cons.1 hchain).1 y (by simp) hxmem'
            exact hxy.trans hzfst.symm

def conjugatedReducedWord (A C : Subgroup G) (P : G)
    (w : HNNExtension.NormalWord.ReducedWord A
      (conjugatePullback A C P) (conjugatePullback A C P)) :
    HNNExtension.NormalWord.ReducedWord G C C where
  head := ((w.head : A) : G) * P⁻¹
  toList := conjugatedList P w.toList
  chain := conjugatedList_chain A C P w.toList w.chain

lemma conjugatedReducedWord_prod (A C : Subgroup G) (P : G)
    (w : HNNExtension.NormalWord.ReducedWord A
      (conjugatePullback A C P) (conjugatePullback A C P))
    (hne : w.toList ≠ []) :
    (conjugatedReducedWord A C P w).prod (MulEquiv.refl C) =
      conjugatedEmbedding A C P (w.prod (MulEquiv.refl (conjugatePullback A C P))) := by
  change
    centralizerOf C (((w.head : A) : G) * P⁻¹) *
        ((conjugatedList P w.toList).map
          (fun p => centralizerStable C ^ (p.1 : ℤ) * centralizerOf C p.2)).prod =
      conjugatedEmbedding A C P
        (HNNExtension.of w.head *
          (w.toList.map
            (fun p => HNNExtension.t ^ (p.1 : ℤ) * HNNExtension.of p.2)).prod)
  rw [conjugatedList_prod A C P w.toList hne]
  simp [conjugatedEmbedding, centralizerOf, map_mul, mul_assoc]

theorem conjugatedEmbedding_preimage_base
    (A C : Subgroup G) (P : G)
    (y : CentralizerHNN A (conjugatePullback A C P))
    (hy : conjugatedEmbedding A C P y ∈
      MonoidHom.range (centralizerOf C)) :
    ∃ a : A, y = HNNExtension.of a := by
  let K := conjugatePullback A C P
  let : Nonempty (HNNExtension.NormalWord.TransversalPair A K K) :=
    HNNExtension.NormalWord.TransversalPair.nonempty _ _ _
  let d : HNNExtension.NormalWord.TransversalPair A K K :=
    Classical.choice inferInstance
  let w : HNNExtension.NormalWord d :=
    (HNNExtension.NormalWord.equiv (MulEquiv.refl K) d) y
  have hwy : w.toReducedWord.prod (MulEquiv.refl K) = y :=
    (HNNExtension.NormalWord.equiv (MulEquiv.refl K) d).symm_apply_apply y
  by_cases hnil : w.toList = []
  · refine ⟨w.head, ?_⟩
    rw [← hwy]
    simp [HNNExtension.NormalWord.ReducedWord.prod, hnil]
  · let wm := conjugatedReducedWord A C P w.toReducedWord
    have hwm : wm.prod (MulEquiv.refl C) = conjugatedEmbedding A C P y := by
      dsimp [wm]
      rw [conjugatedReducedWord_prod A C P w.toReducedWord hnil, hwy]
    have hwbase : wm.prod (MulEquiv.refl C) ∈
        MonoidHom.range (centralizerOf C) := by
      rwa [hwm]
    have hwempty :=
      HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
        (MulEquiv.refl C) wm hwbase
    have : w.toList = [] := by
      cases hlist : w.toList with
      | nil => rfl
      | cons q qs =>
          exfalso
          rcases q with ⟨u, a⟩
          dsimp [wm, conjugatedReducedWord] at hwempty
          rw [hlist] at hwempty
          cases qs <;> simp [conjugatedList] at hwempty
    exact (hnil this).elim

/-- The subgroup generated by an embedded subgroup `A` and the conjugate
`P⁻¹tP` meets the ambient base group exactly in `A`. -/
theorem generatedWith_conjugatedStable_inf_base
    (A C : Subgroup G) (P : G) :
    generatedWith (A.map (centralizerOf C)) (conjugatedStable C P) ⊓
        MonoidHom.range (centralizerOf C) =
      A.map (centralizerOf C) := by
  ext x
  constructor
  · intro hx
    have hxleft := hx.1
    rw [← conjugatedEmbedding_range A C P] at hxleft
    rcases hxleft with ⟨y, hy⟩
    have hybase : conjugatedEmbedding A C P y ∈
        MonoidHom.range (centralizerOf C) := by
      simpa [hy] using hx.2
    rcases conjugatedEmbedding_preimage_base A C P y hybase with ⟨a, rfl⟩
    rw [conjugatedEmbedding_of] at hy
    exact ⟨a, a.property, hy⟩
  · rintro ⟨a, ha, rfl⟩
    constructor
    · apply Subgroup.subset_closure
      exact Or.inl ⟨a, ha, rfl⟩
    · exact ⟨a, rfl⟩

/-- A conjugate of the stable letter cannot lie in the embedded base group.
This is the one-stable-letter case of Britton's lemma. -/
theorem conjugatedStable_not_mem_base (C : Subgroup G) (q : G) :
    conjugatedStable C q ∉ MonoidHom.range (centralizerOf C) := by
  intro hbase
  let w : HNNExtension.NormalWord.ReducedWord G C C :=
    { head := q⁻¹
      toList := [(1, q)]
      chain := List.isChain_singleton _ }
  have hwprod : w.prod (MulEquiv.refl C) = conjugatedStable C q := by
    simp [w, HNNExtension.NormalWord.ReducedWord.prod, conjugatedStable,
      centralizerOf, centralizerStable, mul_assoc]
  have hwbase : w.prod (MulEquiv.refl C) ∈
      MonoidHom.range (centralizerOf C) := by
    rwa [hwprod]
  have hnil :=
    HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
      (MulEquiv.refl C) w hwbase
  simp [w] at hnil

/-- Exact first-coefficient consequence of membership in the subgroup
generated by `A` and `P⁻¹tP`. -/
theorem conjugatedStable_mem_generatedWith_imp_doubleCoset
    (A C : Subgroup G) (P Q : G)
    (hQ : conjugatedStable C Q ∈
      generatedWith (A.map (centralizerOf C)) (conjugatedStable C P)) :
    ∃ c : C, ∃ a : A, P = (c : G) * Q * (a : G) := by
  rw [← conjugatedEmbedding_range A C P] at hQ
  rcases hQ with ⟨y, hy⟩
  let K := conjugatePullback A C P
  let : Nonempty (HNNExtension.NormalWord.TransversalPair A K K) :=
    HNNExtension.NormalWord.TransversalPair.nonempty _ _ _
  let d : HNNExtension.NormalWord.TransversalPair A K K :=
    Classical.choice inferInstance
  let w : HNNExtension.NormalWord d :=
    (HNNExtension.NormalWord.equiv (MulEquiv.refl K) d) y
  have hwy : w.toReducedWord.prod (MulEquiv.refl K) = y :=
    (HNNExtension.NormalWord.equiv (MulEquiv.refl K) d).symm_apply_apply y
  have hne : w.toList ≠ [] := by
    intro hnil
    have hybase : conjugatedEmbedding A C P y ∈
        MonoidHom.range (centralizerOf C) := by
      refine ⟨(w.head : A), ?_⟩
      rw [← hwy]
      simp only [HNNExtension.NormalWord.ReducedWord.prod, hnil,
        List.map_nil, List.prod_nil, mul_one]
      exact (conjugatedEmbedding_of A C P w.head).symm
    exact conjugatedStable_not_mem_base C Q (hy ▸ hybase)
  let wm := conjugatedReducedWord A C P w.toReducedWord
  let qword : HNNExtension.NormalWord.ReducedWord G C C :=
    { head := Q⁻¹
      toList := [(1, Q)]
      chain := List.isChain_singleton _ }
  have hwm : wm.prod (MulEquiv.refl C) =
      conjugatedEmbedding A C P y := by
    dsimp [wm]
    rw [conjugatedReducedWord_prod A C P w.toReducedWord hne, hwy]
  have hqword : qword.prod (MulEquiv.refl C) = conjugatedStable C Q := by
    simp [qword, HNNExtension.NormalWord.ReducedWord.prod,
      conjugatedStable, centralizerOf, centralizerStable, mul_assoc]
  have hprod : wm.prod (MulEquiv.refl C) =
      qword.prod (MulEquiv.refl C) := hwm.trans (hy.trans hqword.symm)
  have hcompare := HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq
    (MulEquiv.refl C) hprod
  cases hlist : w.toList with
  | nil => exact (hne hlist).elim
  | cons p xs =>
      rcases p with ⟨u, aTail⟩
      have hu : u ∈ Option.map Prod.fst wm.toList.head? := by
        dsimp [wm, conjugatedReducedWord]
        rw [hlist]
        cases xs <;> simp [conjugatedList]
      have hdelta' := hcompare.2 u hu
      have hdelta : (((w.head : A) : G) * P⁻¹)⁻¹ * Q⁻¹ ∈ C := by
        simpa [qword, wm, conjugatedReducedWord, conjugated_toSubgroup_self]
          using hdelta'
      let c : C := ⟨(((w.head : A) : G) * P⁻¹)⁻¹ * Q⁻¹, hdelta⟩
      refine ⟨c, w.head, ?_⟩
      dsimp [c]
      simp [mul_assoc]

/-- Lemma B.5 of the paper: intersection inside a centralizer HNN extension. -/
theorem centralizer_intersection
    (Delta L B₀ C : Subgroup G)
    (hCL : C ≤ L) (hCB₀ : C ≤ B₀) (_hCDelta : C ≤ Delta)
    (hinter : (L : Set G) ∩ deltaDoubleCoset Delta B₀ = (C : Set G)) :
    generatedWith (L.map (centralizerOf Delta)) (centralizerStable Delta) ⊓
        generatedWith (B₀.map (centralizerOf Delta)) (centralizerStable Delta) =
      generatedWith (C.map (centralizerOf Delta)) (centralizerStable Delta) :=
  centralizer_intersection_of_doubleCoset Delta L B₀ C hCL hCB₀ hinter

/-- The nested normal-form calculation used in the proof of
Proposition 3.8 of the paper.

Inside the centralizer HNN extension of `G` over `C`, let `p = P⁻¹tP`.
If `A ≤ B₀`, `C ≤ B₀`, `C₀ ≤ C`, and `P ∉ B₀`, then the
subgroup generated by `C₀` and `t` meets

`<A,p> · B₀ · <A,p>`

exactly in the embedded copy of `C₀`.  The proof first takes a reduced
`p`-word with coefficients in `B₀`, substitutes `p = P⁻¹tP`, and compares
it with a reduced `t`-word whose coefficients lie in `C₀`.  A first stable
letter would force `P ∈ B₀`; hence the `p`-length is zero, after which the
restricted-HNN intersection lemma applies. -/
theorem conjugated_doubleCoset_intersection
    (A C B₀ C₀ : Subgroup G)
    (hAB : A ≤ B₀) (hCB : C ≤ B₀) (hC₀C : C₀ ≤ C)
    (P : G) (hP : P ∉ B₀) :
    ((generatedWith (C₀.map (centralizerOf C)) (centralizerStable C) :
        Subgroup (CentralizerHNN G C)) : Set (CentralizerHNN G C)) ∩
        deltaDoubleCoset
          (generatedWith (A.map (centralizerOf C)) (conjugatedStable C P))
          (B₀.map (centralizerOf C)) =
      (C₀.map (centralizerOf C) : Set (CentralizerHNN G C)) := by
  let L : Subgroup (CentralizerHNN G C) :=
    generatedWith (C₀.map (centralizerOf C)) (centralizerStable C)
  let Delta : Subgroup (CentralizerHNN G C) :=
    generatedWith (A.map (centralizerOf C)) (conjugatedStable C P)
  let B₀' : Subgroup (CentralizerHNN G C) := B₀.map (centralizerOf C)
  let Wide : Subgroup (CentralizerHNN G C) :=
    generatedWith (B₀.map (centralizerOf C)) (conjugatedStable C P)
  have hDeltaWide : Delta ≤ Wide := by
    unfold Delta Wide generatedWith
    apply Subgroup.closure_mono
    exact Set.union_subset_union (Subgroup.map_mono hAB) Set.Subset.rfl
  ext x
  constructor
  · rintro ⟨hxL, hxdc⟩
    have hxWide : x ∈ Wide := by
      rcases hxdc with ⟨d₁, hd₁, b, hb, d₂, hd₂, rfl⟩
      exact Wide.mul_mem
        (Wide.mul_mem (hDeltaWide hd₁) (by
          apply Subgroup.subset_closure
          exact Or.inl hb))
        (hDeltaWide hd₂)
    have hxRange : x ∈ MonoidHom.range (conjugatedEmbedding B₀ C P) := by
      rw [conjugatedEmbedding_range B₀ C P]
      exact hxWide
    rcases hxRange with ⟨y, hyx⟩
    let K := conjugatePullback B₀ C P
    let : Nonempty (HNNExtension.NormalWord.TransversalPair B₀ K K) :=
      HNNExtension.NormalWord.TransversalPair.nonempty _ _ _
    let d : HNNExtension.NormalWord.TransversalPair B₀ K K :=
      Classical.choice inferInstance
    let w : HNNExtension.NormalWord d :=
      (HNNExtension.NormalWord.equiv (MulEquiv.refl K) d) y
    have hwy : w.toReducedWord.prod (MulEquiv.refl K) = y :=
      (HNNExtension.NormalWord.equiv (MulEquiv.refl K) d).symm_apply_apply y
    by_cases hnil : w.toList = []
    · have hybase : y = HNNExtension.of w.head := by
        rw [← hwy]
        simp [HNNExtension.NormalWord.ReducedWord.prod, hnil]
      have hxbase : x ∈ MonoidHom.range (centralizerOf C) := by
        refine ⟨(w.head : B₀), ?_⟩
        rw [← hyx, hybase]
        simp [conjugatedEmbedding_of]
      have hcompat : ∀ c : C,
          (c : G) ∈ C₀ ↔ ((MulEquiv.refl C) c : G) ∈ C₀ := by simp
      have hinter := generatedWithStable_inf_base
        (A := C) (B := C) (phi := MulEquiv.refl C) C₀ hcompat
      have hxC₀' : x ∈ C₀.map
          (HNNExtension.of (A := C) (B := C) (φ := MulEquiv.refl C)) := by
        rw [← hinter]
        constructor
        · simpa [L, generatedWith, generatedWithStable,
            centralizerOf, centralizerStable] using hxL
        · exact hxbase
      simpa [centralizerOf] using hxC₀'
    · rcases centralizer_generatedWith_reducedWord C C₀ hxL with
        ⟨wL, hwL, hwLhead, hwLlist⟩
      let wm := conjugatedReducedWord B₀ C P w.toReducedWord
      have hwm : wm.prod (MulEquiv.refl C) = conjugatedEmbedding B₀ C P y := by
        dsimp [wm]
        rw [conjugatedReducedWord_prod B₀ C P w.toReducedWord hnil, hwy]
      have hprod : wm.prod (MulEquiv.refl C) = wL.prod (MulEquiv.refl C) := by
        rw [hwm, hyx, hwL]
      have hcompare := HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq
        (MulEquiv.refl C) hprod
      cases hlist : w.toList with
      | nil => exact (hnil hlist).elim
      | cons q qs =>
          rcases q with ⟨u, b⟩
          have hu : u ∈ Option.map Prod.fst wm.toList.head? := by
            dsimp [wm, conjugatedReducedWord]
            rw [hlist]
            cases qs <;> simp [conjugatedList]
          have hd' := hcompare.2 u hu
          have hd : (((w.head : B₀) : G) * P⁻¹)⁻¹ * wL.head ∈ C := by
            change wm.head⁻¹ * wL.head ∈ C
            simpa [conjugated_toSubgroup_self] using hd'
          have hPin : P ∈ B₀ := by
            have hm := B₀.mul_mem
              (B₀.mul_mem (hCB hd) (B₀.inv_mem (hCB (hC₀C hwLhead))))
              w.head.property
            simpa [mul_assoc] using hm
          exact (hP hPin).elim
  · intro hxC₀
    constructor
    · apply Subgroup.subset_closure
      exact Or.inl hxC₀
    · refine ⟨1, Delta.one_mem, x, ?_, 1, Delta.one_mem, by simp⟩
      exact Subgroup.map_mono (hC₀C.trans hCB) hxC₀

end UniversalGroup.HNNLemmas
