module

public import SmallPresentation.AmalgamNormalForm

/-!
# The torsion theorem for amalgamated products

The cyclic reduction proof in `AmalgamNormalForm` shows that a finite-order element
of an amalgamated product with injective edge maps is conjugate into a vertex group.
The torsion-free corollaries, including the free-product case, follow below.
-/
@[expose] public section

namespace SmallPresentationStatements.ExternalAmalgam

universe u

/-- The classical finite-order conjugacy theorem for an arbitrary nonempty family
of groups amalgamated along injective maps from one group, proved by cyclic reduction. -/
theorem finiteOrder_conjugate_factor {ι : Type*} [Nonempty ι]
    {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
    (φ : ∀ i, H →* G i) (hφ : ∀ i, Function.Injective (φ i))
    (x : Monoid.PushoutI φ) (hx : IsOfFinOrder x) :
    ∃ (i : ι) (g : G i) (c : Monoid.PushoutI φ),
      x = c * Monoid.PushoutI.of i g * c⁻¹ := by
  exact AmalgamNormalForm.finiteOrder_conjugate_factor φ hφ x hx

/-- Injective amalgams of torsion-free groups are torsion-free. -/
theorem pushout_torsionFree {ι : Type*} [Nonempty ι]
    {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
    (φ : ∀ i, H →* G i) (hφ : ∀ i, Function.Injective (φ i))
    [∀ i, IsMulTorsionFree (G i)] : IsMulTorsionFree (Monoid.PushoutI φ) := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro x hx hfinite
  obtain ⟨i, g, c, rfl⟩ := finiteOrder_conjugate_factor φ hφ x hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  have hc : (MulAut.conj c) ((Monoid.PushoutI.of i g : Monoid.PushoutI φ) ^ n) =
      (MulAut.conj c) 1 := by
    simpa only [map_pow, MulAut.conj_apply, map_one] using hpow
  have hi : (Monoid.PushoutI.of i g : Monoid.PushoutI φ) ^ n = 1 :=
    (MulAut.conj c).injective hc
  have hg : g ^ n = 1 := Monoid.PushoutI.of_injective hφ i (by simpa using hi)
  have hg1 : g = 1 := (pow_eq_one_iff_left hn.ne').mp hg
  apply hx
  simp [hg1]

/-- The free-product case follows from the same theorem by amalgamating the trivial group. -/
theorem coprod_torsionFree (A B : Type u) [Group A] [Group B]
    [IsMulTorsionFree A] [IsMulTorsionFree B] : IsMulTorsionFree (Monoid.Coprod A B) := by
  let F : Bool → Type _ := fun b ↦ if b then B else A
  let : ∀ b, Group (F b) := fun b ↦ by cases b <;> dsimp [F] <;> infer_instance
  let : ∀ b, IsMulTorsionFree (F b) :=
    fun b ↦ by cases b <;> dsimp [F] <;> infer_instance
  let φ : ∀ b, PUnit.{1} →* F b := fun _ ↦ 1
  have hφ : ∀ b, Function.Injective (φ b) := fun _ _ _ _ ↦ Subsingleton.elim _ _
  let := pushout_torsionFree φ hφ
  let forward : Monoid.Coprod A B →* Monoid.PushoutI φ :=
    Monoid.Coprod.lift (Monoid.PushoutI.of (φ := φ) false) (Monoid.PushoutI.of (φ := φ) true)
  let family : ∀ b, F b →* Monoid.Coprod A B := fun b ↦
    match b with
    | false => Monoid.Coprod.inl
    | true => Monoid.Coprod.inr
  have hfamily : ∀ b, (family b).comp (φ b) = 1 := by
    intro b
    ext x
    simp [φ]
  let backward : Monoid.PushoutI φ →* Monoid.Coprod A B :=
    Monoid.PushoutI.lift family 1 hfamily
  have hcomp : backward.comp forward = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext <;> ext x <;>
      simp [backward, forward, family, MonoidHom.comp_apply]
  have hinj : Function.Injective forward := by
    intro x y h
    have hx := DFunLike.congr_fun hcomp x
    have hy := DFunLike.congr_fun hcomp y
    exact hx.symm.trans ((congrArg backward h).trans hy)
  exact hinj.isMulTorsionFree forward

end SmallPresentationStatements.ExternalAmalgam
