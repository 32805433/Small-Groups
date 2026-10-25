module

public import SmallPresentation.RelationDerivativeEquivariance

/-! Naturality of the derivative for a map of generator alphabets and a compatible
map of presented groups. The edge-chain map is injective when both maps are. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

/-- Free abelian groups preserve injectivity, without a nonemptiness assumption. -/
theorem freeAbelian_map_injective {A B : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (FreeAbelianGroup.map f) := by
  classical
  let r : FreeAbelianGroup B →+ FreeAbelianGroup A := FreeAbelianGroup.lift (fun b ↦
    if h : ∃ a, f a = b then FreeAbelianGroup.of h.choose else 0)
  have hr (a : A) : r (FreeAbelianGroup.of (f a)) = FreeAbelianGroup.of a := by
    simp only [r, FreeAbelianGroup.lift_apply_of]
    split_ifs with h
    · congr 1
      exact hf h.choose_spec
    · exact (h ⟨a, rfl⟩).elim
  have he : r.comp (FreeAbelianGroup.map f) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro a
    simpa using hr a
  apply Function.LeftInverse.injective (g := r)
  intro z
  exact DFunLike.congr_fun he z

variable {X Y H J : Type} [Group H] [Group J]

/-- Relabel both the initial vertex and the generator of an edge. -/
def chainMap (f : X → Y) (φ : H →* J) : Chains H X →+ Chains J Y :=
  FreeAbelianGroup.map (fun e ↦ (φ e.1, f e.2))

@[simp] theorem chainMap_of (f : X → Y) (φ : H →* J) (h : H) (x : X) :
    chainMap f φ (FreeAbelianGroup.of (h, x)) = FreeAbelianGroup.of (φ h, f x) := rfl

theorem chainMap_shift (f : X → Y) (φ : H →* J) (h : H) (c : Chains H X) :
    chainMap f φ (shift h c) = shift (φ h) (chainMap f φ c) := by
  have he : (chainMap f φ).comp (shift h) = (shift (φ h)).comp (chainMap f φ) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨g, x⟩
    simp
  exact DFunLike.congr_fun he c

theorem chainMap_injective (f : X → Y) (φ : H →* J)
    (hf : Function.Injective f) (hφ : Function.Injective φ) :
    Function.Injective (chainMap f φ) := by
  apply freeAbelian_map_injective
  rintro ⟨g, x⟩ ⟨h, y⟩ he
  exact Prod.ext (hφ (congrArg Prod.fst he)) (hf (congrArg Prod.snd he))

variable (p : FreeGroup X →* H) (q : FreeGroup Y →* J)
  (f : X → Y) (φ : H →* J)
  (hcompat : q.comp (FreeGroup.map f) = φ.comp p)

include hcompat in
/-- The derivative commutes with the specified generator and quotient maps. -/
theorem derivative_natural (w : FreeGroup X) :
    derivative q (FreeGroup.map f w) = chainMap f φ (derivative p w) := by
  have hc (u : FreeGroup X) : q (FreeGroup.map f u) = φ (p u) :=
    DFunLike.congr_fun hcompat u
  induction w using FreeGroup.induction_on with
  | one => simp
  | of x => simp
  | inv_of x ih =>
    rw [map_inv, derivative_inv, derivative_inv, map_neg, chainMap_shift, hc, map_inv, ih]
  | mul u v hu hv =>
    rw [map_mul, derivative_mul, derivative_mul, map_add, chainMap_shift, hu, hv, hc]

/-- The compatible map restricted to the presentation kernels. -/
def kernelMap : p.ker →* q.ker :=
  ((FreeGroup.map f).comp p.ker.subtype).codRestrict q.ker (by
    intro k
    change q (FreeGroup.map f k.val) = 1
    have hc := DFunLike.congr_fun hcompat k.val
    change q (FreeGroup.map f k.val) = φ (p k.val) at hc
    rw [hc, show p k.val = 1 from k.property, map_one])

/-- The natural map of relation abelianizations. -/
def relationMap : Additive (Abelianization p.ker) →+ Additive (Abelianization q.ker) :=
  (Abelianization.map (kernelMap p q f φ hcompat)).toAdditive

theorem relationDerivative_natural (c : Additive (Abelianization p.ker)) :
    relationDerivative q (relationMap p q f φ hcompat c) =
      chainMap f φ (relationDerivative p c) := by
  induction c using QuotientGroup.induction_on with
  | H k =>
    change derivative q (FreeGroup.map f k.val) = chainMap f φ (derivative p k.val)
    exact derivative_natural p q f φ hcompat k.val

/-- Factor-supported relation modules embed whenever their generators and groups do. -/
theorem relationMap_injective (hp : Function.Surjective p)
    (hf : Function.Injective f) (hφ : Function.Injective φ) :
    Function.Injective (relationMap p q f φ hcompat) := by
  intro c d he
  apply relationDerivative_injective p hp
  apply chainMap_injective f φ hf hφ
  rw [← relationDerivative_natural p q f φ hcompat,
    ← relationDerivative_natural p q f φ hcompat, he]

end SmallPresentationStatements.RelationDerivative
