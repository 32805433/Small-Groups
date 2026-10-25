module

public import SmallPresentation.UniversalCentralExtension
public import SmallPresentation.MitosisModel

/-!
# Algebraic lifting through two mitoses

Commuting images modulo a central kernel have exactly commuting derived images.
This permits a corrected lift on the derived group; the first mitosis sends the
original group into the derived group of the second mitosis's source.
-/
@[expose] public section

namespace SmallPresentationStatements.MitosisLifting

open scoped commutatorElement
open UniversalCentralExtension

variable {P K E B : Type} [Group P] [Group K] [Group E] [Group B]

/-- Commutation modulo a central kernel becomes exact after deriving either factor. -/
theorem derived_commute (π : E →* B) (hc : Central π) (a b : P →* E)
    (hcomm : ∀ x y, Commute (π (a x)) (π (b y)))
    (x : commutator P) (y : P) : Commute (a x.val) (b y) := by
  have hab : ⁅a.range, b.range⁆ ≤ π.ker := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    change π ⁅a u, b v⁆ = 1
    rw [map_commutatorElement]
    exact (hcomm u v).commutator_eq
  have hcentral : ⁅a.range, b.range⁆ ≤ Subgroup.center E := hab.trans hc
  have hzero (S : Subgroup E) : ⁅⁅a.range, b.range⁆, S⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    exact (Subgroup.commutator_mono hcentral le_rfl).trans_eq
      (Subgroup.commutator_center_left S)
  have hderived : ⁅⁅a.range, a.range⁆, b.range⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (hzero a.range)
      (by simpa only [Subgroup.commutator_comm b.range a.range] using hzero a.range)
  have hx : a x.val ∈ ⁅a.range, a.range⁆ := by
    rw [← map_commutator_eq]
    exact Subgroup.mem_map_of_mem a x.property
  have hz := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hderived) hx
  exact ((Subgroup.mem_centralizer_iff.mp hz) (b y) ⟨y, rfl⟩).symm

def multiply (a b : P →* E) (h : ∀ x y, Commute (a x) (b y)) : P →* E :=
  (a.noncommCoprod b h).comp ((MonoidHom.id P).prod (MonoidHom.id P))

@[simp] theorem multiply_apply (a b : P →* E) (h : ∀ x y, Commute (a x) (b y)) (x : P) :
    multiply a b h x = a x * b x := rfl

def derivedMap (q : P →* K) (hq : Function.Surjective q) :
    commutator P →* commutator K :=
  (q.comp (commutator P).subtype).codRestrict (commutator K) (fun x ↦ by
    have hmem : q x.val ∈ (commutator P).map q := Subgroup.mem_map_of_mem q x.property
    rwa [map_commutator_of_surjective hq] at hmem)

theorem derivedMap_surjective (q : P →* K) (hq : Function.Surjective q) :
    Function.Surjective (derivedMap q hq) := by
  intro x
  have hx : x.val ∈ (commutator P).map q := by
    rw [map_commutator_of_surjective hq]
    exact x.property
  obtain ⟨y, hy, heq⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

/-- The diagonal and swap lifts produce a homomorphism on the derived source.
The correction kills the pullback kernel, so it descends to the actual derived group. -/
theorem corrected_derived_lift (π : E →* B) (hc : Central π)
    (q : P →* K) (hq : Function.Surjective q) (i : K →* B)
    (a b c : P →* E) (ha : π.comp a = i.comp q)
    (hcomm : ∀ x y, Commute (π (a x)) (π (b y)))
    (hdiag : ∀ x, π (c x) = π (a x) * π (b x))
    (hker : ∀ x ∈ q.ker, b x = a x ∧ c x = a x) :
    ∃ σ : commutator K →* E, π.comp σ = i.comp (commutator K).subtype := by
  let a' := a.comp (commutator P).subtype
  let b' := b.comp (commutator P).subtype
  let c' := c.comp (commutator P).subtype
  have hcomm' (x y : commutator P) : Commute (a' x) (b' y) :=
    derived_commute π hc a b hcomm x y.val
  let product := multiply a' b' hcomm'
  have heq : π.comp c' = π.comp product := by
    ext x
    change π (c x.val) = π (a x.val * b x.val)
    rw [map_mul]
    exact hdiag x.val
  let δ := differenceHom π hc c' product heq
  have hδ (x : commutator P) : δ x ∈ π.ker := by
    change π (c' x * (product x)⁻¹) = 1
    rw [map_mul, map_inv, show π (c' x) = π (product x) from DFunLike.congr_fun heq x]
    exact mul_inv_cancel _
  have hcentral (x y : commutator P) : Commute (a' x) (δ y) :=
    (Subgroup.mem_center_iff.mp (hc (hδ y))) (a' x)
  let corrected := multiply a' δ hcentral
  have hproject (x : commutator P) : π (corrected x) = i (q x.val) := by
    change π (a' x * δ x) = _
    rw [map_mul, show π (δ x) = 1 from hδ x, mul_one]
    exact DFunLike.congr_fun ha x.val
  have hkill : (derivedMap q hq).ker ≤ corrected.ker := by
    intro x hx
    have hx' : q x.val = 1 := congrArg Subtype.val hx
    obtain ⟨hb, hc'⟩ := hker x.val hx'
    change a x.val * (c x.val * (a x.val * b x.val)⁻¹) = 1
    rw [hb, hc']
    group
  let σ := (derivedMap q hq).liftOfSurjective (derivedMap_surjective q hq) ⟨corrected, hkill⟩
  have hσ : σ.comp (derivedMap q hq) = corrected :=
    MonoidHom.liftOfRightInverse_comp ..
  refine ⟨σ, ?_⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := derivedMap_surjective q hq x
  exact (congrArg π (DFunLike.congr_fun hσ y)).trans (hproject y)

/-- Every map from one mitosis lifts on the derived subgroup of its source
through any central extension. -/
theorem lift_derived_mitosis (π : E →* B) (hπ : Function.Surjective π) (hc : Central π)
    (f : MitosisModel.Model K →* B) :
    ∃ σ : commutator K →* E,
      π.comp σ = (f.comp (MitosisModel.inclusion K)).comp (commutator K).subtype := by
  let i := f.comp (MitosisModel.inclusion K)
  let R := CentralPullback.group π i
  let q : R →* K := CentralPullback.second π i
  let a : R →* E := CentralPullback.first π i
  have hq : Function.Surjective q := CentralPullback.second_surjective π i hπ
  obtain ⟨S, hS⟩ := hπ (f (MitosisModel.s K))
  obtain ⟨D, hD⟩ := hπ (f (MitosisModel.d K))
  let b : R →* E := (MulAut.conj S⁻¹).toMonoidHom.comp a
  let c : R →* E := (MulAut.conj D⁻¹).toMonoidHom.comp a
  have ha (x : R) : π (a x) = f (MitosisModel.inclusion K (q x)) := x.property
  have hb (x : R) : π (b x) = f (MitosisModel.second K (q x)) := by
    simp only [b, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [map_mul, map_mul, map_inv, hS, ha]
    rw [← map_inv, ← map_mul, ← map_mul, MitosisModel.swap_action]
  have hd (x : R) : π (c x) = π (a x) * π (b x) := by
    simp only [c, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [map_mul, map_mul, map_inv, hD, ha, hb]
    rw [← map_inv, ← map_mul, ← map_mul, MitosisModel.diagonal_action, map_mul]
  apply corrected_derived_lift π hc q hq i a b c
  · ext x
    exact ha x
  · intro x y
    rw [ha, hb]
    exact (MitosisModel.copies_commute K (q x) (q y)).map f
  · exact hd
  · intro x hx
    have hax : a x ∈ π.ker := by
      change π (a x) = 1
      rw [ha, show q x = 1 from hx, map_one, map_one]
    have hfix (T : E) : T⁻¹ * a x * T = a x := by
      rw [mul_assoc, (central_iff π).mp hc (a x) hax T]
      simp
    constructor
    · simpa only [b, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hfix S
    · simpa only [c, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hfix D

/-- The first-copy inclusion of a mitosis lands in its derived subgroup. -/
theorem inclusion_mem_commutator (J : Type) [Group J] (x : J) :
    MitosisModel.inclusion J x ∈ commutator (MitosisModel.Model J) := by
  have hconj (s z : MitosisModel.Model J) :
      Abelianization.of (s⁻¹ * z * s) = Abelianization.of z := by
    rw [map_mul, map_mul, map_inv,
      mul_comm (Abelianization.of s)⁻¹ (Abelianization.of z), mul_assoc,
      inv_mul_cancel, mul_one]
  have hs : Abelianization.of (MitosisModel.inclusion J x) =
      Abelianization.of (MitosisModel.second J x) := by
    have h := congrArg (Abelianization.of : MitosisModel.Model J →*
      Abelianization (MitosisModel.Model J)) (MitosisModel.swap_action J x)
    simpa only [hconj, map_mul] using h
  have hd : Abelianization.of (MitosisModel.inclusion J x) =
      Abelianization.of (MitosisModel.inclusion J x) *
        Abelianization.of (MitosisModel.second J x) := by
    have h := congrArg (Abelianization.of : MitosisModel.Model J →*
      Abelianization (MitosisModel.Model J)) (MitosisModel.diagonal_action J x)
    simpa only [hconj, map_mul] using h
  have hz : Abelianization.of (MitosisModel.second J x) = 1 := mul_eq_left.mp hd.symm
  exact (QuotientGroup.eq_one_iff _).mp (hs.trans hz)

noncomputable def intoDerived (J : Type) [Group J] :
    J →* commutator (MitosisModel.Model J) :=
  (MitosisModel.inclusion J).codRestrict _ (inclusion_mem_commutator J)

/-- Two successive mitoses lift the original group through every central extension.
No homology calculation or hypothesis on the abelianization is needed. -/
theorem double_mitosis_lift (J : Type) [Group J]
    (π : E →* B) (hπ : Function.Surjective π) (hc : Central π)
    (f : MitosisModel.Model (MitosisModel.Model J) →* B) :
    ∃ σ : J →* E, π.comp σ =
      (f.comp (MitosisModel.inclusion (MitosisModel.Model J))).comp (MitosisModel.inclusion J) := by
  obtain ⟨s, hs⟩ := lift_derived_mitosis π hπ hc f
  refine ⟨s.comp (intoDerived J), ?_⟩
  ext x
  exact DFunLike.congr_fun hs (intoDerived J x)

/-- The lift detects the original group whenever the displayed map into the base does. -/
theorem double_mitosis_lift_injective (J : Type) [Group J]
    (π : E →* B) (hπ : Function.Surjective π) (hc : Central π)
    (f : MitosisModel.Model (MitosisModel.Model J) →* B)
    (hinj : Function.Injective
      ((f.comp (MitosisModel.inclusion (MitosisModel.Model J))).comp (MitosisModel.inclusion J))) :
    ∃ σ : J →* E, Function.Injective σ ∧ π.comp σ =
      (f.comp (MitosisModel.inclusion (MitosisModel.Model J))).comp (MitosisModel.inclusion J) := by
  obtain ⟨σ, hσ⟩ := double_mitosis_lift J π hπ hc f
  refine ⟨σ, ?_, hσ⟩
  intro x y hxy
  apply hinj
  exact (DFunLike.congr_fun hσ x).symm.trans
    ((congrArg π hxy).trans (DFunLike.congr_fun hσ y))

section FinitePresentations

variable {n r : ℕ} (T : FP n r)

theorem finite_source_mem_commutator (x : T.Group) :
    MitosisModel.source T x ∈ commutator (MitosisWords.presentation T).Group := by
  let e := MitosisModel.presentationEquiv T
  have hm : MitosisModel.inclusion T.Group x ∈
      (commutator (MitosisWords.presentation T).Group).map e.toMonoidHom := by
    rw [map_commutator_of_surjective (f := e.toMonoidHom) e.surjective]
    exact inclusion_mem_commutator T.Group x
  obtain ⟨y, hy, he⟩ := hm
  have hs : e (MitosisModel.source T x) = MitosisModel.inclusion T.Group x :=
    DFunLike.congr_fun (MitosisModel.toModel_source T) x
  exact e.injective (he.trans hs.symm) ▸ hy

noncomputable def finiteIntoDerived :
    T.Group →* commutator (MitosisWords.presentation T).Group :=
  (MitosisModel.source T).codRestrict _ (finite_source_mem_commutator T)

/-- The algebraic lift follows the actual old-generator maps in the two successive
finite presentations. Thus it applies directly to the manuscript's literal mitoses. -/
theorem finite_double_lift (π : E →* B) (hπ : Function.Surjective π) (hc : Central π)
    (f : (MitosisWords.presentation (MitosisWords.presentation T)).Group →* B) :
    ∃ σ : T.Group →* E, π.comp σ =
      (f.comp (MitosisModel.source (MitosisWords.presentation T))).comp (MitosisModel.source T) := by
  let e := MitosisModel.presentationEquiv (MitosisWords.presentation T)
  obtain ⟨s, hs⟩ := lift_derived_mitosis π hπ hc (f.comp e.symm.toMonoidHom)
  refine ⟨s.comp (finiteIntoDerived T), ?_⟩
  apply MonoidHom.ext
  intro x
  calc
    π (s (finiteIntoDerived T x)) =
        f (MitosisModel.fromModel (MitosisWords.presentation T)
          (MitosisModel.inclusion (MitosisWords.presentation T).Group (MitosisModel.source T x))) :=
      DFunLike.congr_fun hs (finiteIntoDerived T x)
    _ = _ := congrArg f (MitosisModel.fromModel_inclusion (MitosisWords.presentation T) _)

theorem finite_double_lift_injective (π : E →* B) (hπ : Function.Surjective π)
    (hc : Central π)
    (f : (MitosisWords.presentation (MitosisWords.presentation T)).Group →* B)
    (hf : Function.Injective f) :
    ∃ σ : T.Group →* E, Function.Injective σ ∧ π.comp σ =
      (f.comp (MitosisModel.source (MitosisWords.presentation T))).comp (MitosisModel.source T) := by
  obtain ⟨σ, hσ⟩ := finite_double_lift T π hπ hc f
  refine ⟨σ, ?_, hσ⟩
  intro x y hxy
  apply MitosisModel.source_injective T
  apply MitosisModel.source_injective (MitosisWords.presentation T)
  apply hf
  exact (DFunLike.congr_fun hσ x).symm.trans
    ((congrArg π hxy).trans (DFunLike.congr_fun hσ y))

end FinitePresentations

end SmallPresentationStatements.MitosisLifting
