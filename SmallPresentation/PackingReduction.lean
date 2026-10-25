module

public import SmallPresentation.PackingKernel
public import SmallPresentation.KernelSandwich

/-! # The algebraic reduction of packing to affine slot placement and a detector map -/
public section

namespace SmallPresentationStatements.PackingReduction

open scoped commutatorElement

variable {A G B C : Type} [Group A] [Group G] [Group B] [Group C]

/-- A map into the affine quotient detects the upper kernel inclusion even when
the base quotient `B` is not itself a quotient of the full output `G`. -/
theorem upper_of_detector (f : A →* G) (g : A →* B)
    (ψ : G →* C) (k : B →* C) (hk : Function.Injective k)
    (hcompat : ψ.comp f = k.comp g) : f.ker ≤ g.ker := by
  intro a ha
  apply hk
  have h := DFunLike.congr_fun hcompat a
  simp only [MonoidHom.comp_apply] at h
  change k (g a) = k 1
  rw [← h, show f a = 1 from ha, map_one, map_one]

/-- Propagate commutation from the specified base generators to every base element. -/
theorem commute_all_of_generators (f : A →* G) (S : Set A)
    (hgen : Subgroup.closure S = ⊤) (z : G)
    (hz : ∀ a ∈ S, Commute z (f a)) : ∀ a, Commute z (f a) := by
  have h : Subgroup.closure S ≤ (Subgroup.centralizer ({z} : Set G)).comap f := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    change ∀ b ∈ ({z} : Set G), b * f a = f a * b
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact hz a ha
  intro a
  have ha : a ∈ (Subgroup.centralizer ({z} : Set G)).comap f := by
    apply h
    rw [hgen]
    trivial
  exact ha z (Set.mem_singleton z)

/-- Isolating every row against every generator proves the entire lower inclusion,
including the normal closure, not only commutation of the two encoded letters. -/
theorem lower_of_slots (f : A →* G) (S R : Set A) (hgen : Subgroup.closure S = ⊤)
    (hslots : ∀ r ∈ R, ∀ a ∈ S, ∃ (n : ℕ) (v : Fin n → G) (j : Fin n),
      v j = f r ∧ Commute (List.ofFn v).prod (f a) ∧
        ∀ i, i ≠ j → Commute (v i) (f a)) :
    ⁅Subgroup.normalClosure R, (⊤ : Subgroup A)⁆ ≤ f.ker := by
  have hrows : ∀ r ∈ R, ∀ a, Commute (f r) (f a) := by
    intro r hr
    apply commute_all_of_generators f S hgen
    intro a ha
    obtain ⟨n, v, j, hj, htotal, hother⟩ := hslots r hr a ha
    rw [← hj]
    exact PackingKernel.commute_of_stored_product v j (f a) htotal hother
  have hcenter : ∀ r ∈ R, f.rangeRestrict r ∈ Subgroup.center f.range := by
    intro r hr
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨a, ha⟩ := y.property
    apply Subtype.ext
    change y.val * f r = f r * y.val
    rw [← ha]
    exact (hrows r hr a).symm
  have h := PackingKernel.commutator_normalClosure_le_kernel f.rangeRestrict R hcenter
  simpa only [MonoidHom.ker_rangeRestrict] using h

/-- Common final embedding argument for the packed and absorbed presentations. -/
theorem source_embeds {Q : Type} [Group Q] (hQ : CentrallyClosed Q)
    (f : A →* G) (g : A →* B) (hg : Function.Surjective g)
    (S R : Set A) (hgen : Subgroup.closure S = ⊤) (hR : g.ker = Subgroup.normalClosure R)
    (ψ : G →* C) (k : B →* C) (hk : Function.Injective k)
    (hcompat : ψ.comp f = k.comp g)
    (hslots : ∀ r ∈ R, ∀ a ∈ S, ∃ (n : ℕ) (v : Fin n → G) (j : Fin n),
      v j = f r ∧ Commute (List.ofFn v).prod (f a) ∧
        ∀ i, i ≠ j → Commute (v i) (f a))
    (e : Q →* B) (he : Function.Injective e) : ∃ σ : Q →* G, Function.Injective σ := by
  apply KernelSandwich.embedding_of_sandwich hQ f g hg
    (upper_of_detector f g ψ k hk hcompat) _ e he
  rw [hR]
  exact lower_of_slots f S R hgen hslots

end SmallPresentationStatements.PackingReduction
