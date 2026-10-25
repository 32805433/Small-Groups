module

public import SmallPresentation.StructuralDefinitions
public import SmallPresentation.CentralDefects

/-!
# Lifting through central extensions

The pullback construction used in both packing proofs is explicit here. Only the
central-extension splitting property of the source is assumed; no embedding into
the total space is included in the hypotheses.
-/
@[expose] public section

namespace SmallPresentationStatements

namespace CentralPullback

variable {E B Q : Type} [Group E] [Group B] [Group Q]

def group (π : E →* B) (f : Q →* B) : Subgroup (E × Q) where
  carrier := {x | π x.1 = f x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change π x.1 = f x.2 at hx
    change π y.1 = f y.2 at hy
    change π (x.1 * y.1) = f (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change π x.1 = f x.2 at hx
    change π x.1⁻¹ = f x.2⁻¹
    rw [map_inv, map_inv, hx]

def first (π : E →* B) (f : Q →* B) : group π f →* E :=
  (MonoidHom.fst E Q).comp (group π f).subtype

def second (π : E →* B) (f : Q →* B) : group π f →* Q :=
  (MonoidHom.snd E Q).comp (group π f).subtype

theorem second_surjective (π : E →* B) (f : Q →* B)
    (hπ : Function.Surjective π) : Function.Surjective (second π f) := by
  intro q
  obtain ⟨e, he⟩ := hπ (f q)
  exact ⟨⟨(e, q), he⟩, rfl⟩

theorem kernel_central (π : E →* B) (f : Q →* B)
    (hcentral : ∀ z ∈ π.ker, ∀ x : E, z * x = x * z) :
    ∀ z ∈ (second π f).ker, ∀ x, z * x = x * z := by
  intro z hz x
  have hz₂ : z.val.2 = 1 := hz
  have hz₁ : z.val.1 ∈ π.ker := by
    change π z.val.1 = 1
    rw [z.property, hz₂, map_one]
  apply Subtype.ext
  apply Prod.ext
  · exact hcentral _ hz₁ _
  · change z.val.2 * x.val.2 = x.val.2 * z.val.2
    simp [hz₂]

end CentralPullback

/-- Pull back the extension and compose its section with the first projection. -/
theorem CentrallyClosed.lift {Q E B : Type} [Group Q] [Group E] [Group B]
    (hQ : CentrallyClosed Q) (π : E →* B) (hπ : Function.Surjective π)
    (hcentral : ∀ z ∈ π.ker, ∀ x : E, z * x = x * z) (f : Q →* B) :
    ∃ σ : Q →* E, π.comp σ = f := by
  obtain ⟨s, hs⟩ := hQ (CentralPullback.group π f) (CentralPullback.second π f)
    (CentralPullback.second_surjective π f hπ) (CentralPullback.kernel_central π f hcentral)
  refine ⟨(CentralPullback.first π f).comp s, ?_⟩
  ext q
  have hsq : (s q).val.2 = q := DFunLike.congr_fun hs q
  change π (s q).val.1 = f q
  rw [(s q).property, hsq]

theorem CentrallyClosed.lift_injective {Q E B : Type} [Group Q] [Group E] [Group B]
    (hQ : CentrallyClosed Q) (π : E →* B) (hπ : Function.Surjective π)
    (hcentral : ∀ z ∈ π.ker, ∀ x : E, z * x = x * z)
    (f : Q →* B) (hf : Function.Injective f) :
    ∃ σ : Q →* E, π.comp σ = f ∧ Function.Injective σ := by
  obtain ⟨σ, hσ⟩ := hQ.lift π hπ hcentral f
  refine ⟨σ, hσ, ?_⟩
  intro x y hxy
  apply hf
  have hx := DFunLike.congr_fun hσ x
  have hy := DFunLike.congr_fun hσ y
  exact hx.symm.trans ((congrArg π hxy).trans hy)

/-- Central closedness is invariant under an explicit group isomorphism. -/
theorem CentrallyClosed.of_equiv {H G : Type} [Group H] [Group G]
    (hH : CentrallyClosed H) (e : H ≃* G) : CentrallyClosed G := by
  intro E _ π hπ hc
  obtain ⟨σ, hσ⟩ := hH.lift π hπ hc e.toMonoidHom
  refine ⟨σ.comp e.symm.toMonoidHom, ?_⟩
  ext g
  have h := DFunLike.congr_fun hσ (e.symm g)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    MonoidHom.id_apply] using h

/-- The purely group-theoretic part of the five-term splitting argument. The
homology input is precisely the trivial intersection of the kernel with the
derived subgroup. -/
theorem split_of_commutator_kernel {E Q : Type*} [Group E] [Group Q]
    (π : E →* Q) (hπ : Function.Surjective π) (hQ : commutator Q = ⊤)
    (hker : ∀ z ∈ π.ker, z ∈ commutator E → z = 1) :
    ∃ σ : Q →* E, π.comp σ = MonoidHom.id Q := by
  let f : commutator E →* Q := π.comp (commutator E).subtype
  have hf : Function.Bijective f := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff f).mp
      apply bot_unique
      intro z hz
      have hz' : π z.val = 1 := hz
      have heq := hker z.val hz' z.property
      change z = 1
      exact Subtype.ext heq
    · intro q
      have hmem : q ∈ (commutator E).map π := by
        rw [map_commutator_of_surjective hπ, hQ]
        trivial
      obtain ⟨z, hz, hπz⟩ := hmem
      exact ⟨⟨z, hz⟩, hπz⟩
  let e : commutator E ≃* Q := MulEquiv.ofBijective f hf
  refine ⟨(commutator E).subtype.comp e.symm.toMonoidHom, ?_⟩
  ext q
  exact e.apply_symm_apply q

/-- The explicit corrected words in both packing theorems are the images of an
injective lift. Their equality to the split generators is proved, not assumed. -/
theorem Normalized.lift_corrected {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q)
    (hC : CentrallyClosed Q.Group) {E B : Type} [Group E] [Group B]
    (π : E →* B) (hπ : Function.Surjective π)
    (hcentral : ∀ z ∈ π.ker, ∀ x : E, z * x = x * z)
    (f : Q.Group →* B) (hf : Function.Injective f) (X Y : E)
    (hX : π X = f (PresentedGroup.of 0)) (hY : π Y = f (PresentedGroup.of 1)) :
    ∃ σ : Q.Group →* E, Function.Injective σ ∧ π.comp σ = f ∧
      σ (PresentedGroup.of 0) = X *
        (Word.eval ![X, Y] (Q.relator ⟨0, lt_of_lt_of_le (by decide) hQ.1⟩))⁻¹ ∧
      σ (PresentedGroup.of 1) = Y *
        (Word.eval ![X, Y] (Q.relator ⟨1, lt_of_lt_of_le (by decide) hQ.1⟩))⁻¹ := by
  obtain ⟨σ, hσ, hσinj⟩ := hC.lift_injective π hπ hcentral f hf
  let q₁ := σ (PresentedGroup.of 0)
  let q₂ := σ (PresentedGroup.of 1)
  let c₁ := q₁⁻¹ * X
  let c₂ := q₂⁻¹ * Y
  have hq₁ : π q₁ = f (PresentedGroup.of 0) := DFunLike.congr_fun hσ _
  have hq₂ : π q₂ = f (PresentedGroup.of 1) := DFunLike.congr_fun hσ _
  have hc₁ : c₁ ∈ π.ker := by simp [c₁, MonoidHom.mem_ker, hq₁, hX]
  have hc₂ : c₂ ∈ π.ker := by simp [c₂, MonoidHom.mem_ker, hq₂, hY]
  have hrows (i : Fin L) : Word.eval ![q₁, q₂] (Q.relator i) = 1 := by
    have hgen : (![q₁, q₂] : Fin 2 → E) =
        fun j ↦ σ (PresentedGroup.of (rels := Q.relSet) j) := by
      funext j
      fin_cases j <;> rfl
    rw [hgen, ← Word.map_eval, Q.eval_relator, map_one]
  have hcorr := hQ.corrected_generators q₁ q₂ c₁ c₂
    (hcentral c₁ hc₁) (hcentral c₂ hc₂) hrows
  have hx : q₁ * c₁ = X := by simp [c₁]
  have hy : q₂ * c₂ = Y := by simp [c₂]
  rw [hx, hy] at hcorr
  exact ⟨σ, hσinj, hσ, hcorr.1.symm, hcorr.2.symm⟩

end SmallPresentationStatements
