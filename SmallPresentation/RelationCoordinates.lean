module

public import SmallPresentation.RelationExtension
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Tactic.Group

/-! Central relation coordinates for arbitrary groups and arbitrary families of relators.
Normal generation always gives surjectivity. Independence follows from a Cohen–Lyndon
free conjugate basis, a structural condition on the normal subgroup before taking coinvariants. -/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates

open RelationExtension

variable {F I : Type} [Group F] (rel : I → F)

abbrev Relations := Subgroup.normalClosure (Set.range rel)

/-- The distinguished relator in the central relation coinvariants. -/
def relator (i : I) : Kernel (Relations rel) :=
  ⟨QuotientGroup.mk' (commutatorKernel (Relations rel)) (rel i), by
    change QuotientGroup.mk' (Relations rel) (rel i) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩)⟩

/-- The canonical map from relator exponent vectors to central relation coinvariants. -/
def coordinates : FreeAbelianGroup I →+ Additive (Kernel (Relations rel)) :=
  FreeAbelianGroup.lift (fun i ↦ Additive.ofMul (relator rel i))

@[simp] theorem coordinates_of (i : I) :
    coordinates rel (FreeAbelianGroup.of i) = Additive.ofMul (relator rel i) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Normal generation suffices for surjectivity; no asphericity or word condition is needed. -/
theorem coordinates_surjective : Function.Surjective (coordinates rel) := by
  let c := ((projection (Relations rel)).ker.subtype).comp
    (coordinates rel).toMultiplicativeLeft
  have hc : c.range ≤ Subgroup.center (Total (Relations rel)) := by
    rintro z ⟨x, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun y ↦
      (kernel_central (Relations rel) _ ((coordinates rel).toMultiplicativeLeft x).property y).symm)
  let : c.range.Normal := Subgroup.normal_of_le_center hc
  have hN : Relations rel ≤ c.range.comap (QuotientGroup.mk' (commutatorKernel (Relations rel))) := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (FreeAbelianGroup.of i),
      congrArg (fun z : Additive (Kernel (Relations rel)) ↦ z.toMul.val) (coordinates_of rel i)⟩
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (commutatorKernel (Relations rel)) z.toMul.val
  have hxN : x ∈ Relations rel := by
    apply (QuotientGroup.eq_one_iff x).mp
    change projection (Relations rel) (QuotientGroup.mk' (commutatorKernel (Relations rel)) x) = 1
    rw [hx]
    exact z.toMul.property
  obtain ⟨v, hv⟩ := hN hxN
  refine ⟨v.toAdd, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hv.trans hx

/-- The quotient map from the normal subgroup to its central coinvariants. -/
def toCoinvariants (N : Subgroup F) [N.Normal] : N →* Kernel N where
  toFun n := ⟨QuotientGroup.mk' (commutatorKernel N) n.val, by
    change QuotientGroup.mk' N n.val = 1
    exact (QuotientGroup.eq_one_iff _).mpr n.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] theorem toCoinvariants_val (N : Subgroup F) [N.Normal] (n : N) :
    (toCoinvariants N n).val = QuotientGroup.mk' (commutatorKernel N) n.val := rfl

theorem toCoinvariants_surjective (N : Subgroup F) [N.Normal] :
    Function.Surjective (toCoinvariants N) := by
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (commutatorKernel N) z.val
  have hxN : x ∈ N := by
    apply (QuotientGroup.eq_one_iff x).mp
    change projection N (QuotientGroup.mk' (commutatorKernel N) x) = 1
    rw [hx]
    exact z.property
  exact ⟨⟨x, hxN⟩, Subtype.ext hx⟩

/-- A Cohen–Lyndon basis is an actual free basis of the normal closure, indexed by
relators and quotient cosets. Its generators are conjugates using coset representatives.
No assertion about central coinvariants or homology is included in this condition. -/
structure ConjugateBasis where
  representative : I → (F ⧸ Relations rel) → F
  representative_mk : ∀ i q, QuotientGroup.mk' (Relations rel) (representative i q) = q
  equiv : FreeGroup (I × (F ⧸ Relations rel)) ≃* Relations rel
  equiv_of : ∀ i q, (equiv (FreeGroup.of (i, q))).val =
    representative i q * rel i * (representative i q)⁻¹

open scoped commutatorElement

/-- Conjugation acts on every normal subgroup. -/
def conjugation (N : Subgroup F) [N.Normal] (f : F) : N →* N where
  toFun n := ⟨f * n.val * f⁻¹, Subgroup.Normal.conj_mem inferInstance _ n.property f⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

/-- A conjugation-invariant homomorphism kills all ambient commutators. -/
theorem commutator_le_ker_of_conjugation_invariant
    (N : Subgroup F) [N.Normal] {C : Type} [Group C] (φ : N →* C)
    (hinvariant : ∀ f n, φ (conjugation N f n) = φ n) :
    (toCoinvariants N).ker ≤ φ.ker := by
  let K := φ.ker.map N.subtype
  have hcomm : commutatorKernel N ≤ K := by
    apply Subgroup.commutator_le.mpr
    intro n hn f _
    let x : N := ⟨n, hn⟩
    have heq : (x * conjugation N f x⁻¹).val = ⁅n, f⁆ := by
      simp [conjugation, commutatorElement_def, mul_assoc, x]
    refine ⟨x * conjugation N f x⁻¹, ?_, heq⟩
    change φ (x * conjugation N f x⁻¹) = 1
    rw [map_mul, hinvariant, map_inv, mul_inv_cancel]
  intro n hn
  have hval : n.val ∈ commutatorKernel N := by
    apply (QuotientGroup.eq_one_iff n.val).mp
    exact congrArg Subtype.val hn
  obtain ⟨x, hx, hxn⟩ := hcomm hval
  have heq : x = n := Subtype.ext hxn
  change φ x = 1 at hx
  change φ n = 1
  simpa only [heq] using hx

/-- Descend any conjugation-invariant homomorphism to the central coinvariants. -/
noncomputable def liftInvariant
    (N : Subgroup F) [N.Normal] {C : Type} [Group C] (φ : N →* C)
    (hinvariant : ∀ f n, φ (conjugation N f n) = φ n) : Kernel N →* C :=
  (toCoinvariants N).liftOfSurjective (toCoinvariants_surjective N)
    ⟨φ, commutator_le_ker_of_conjugation_invariant N φ hinvariant⟩

@[simp] theorem liftInvariant_toCoinvariants
    (N : Subgroup F) [N.Normal] {C : Type} [Group C] (φ : N →* C)
    (hinvariant : ∀ f n, φ (conjugation N f n) = φ n) (n : N) :
    liftInvariant N φ hinvariant (toCoinvariants N n) = φ n := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

namespace ConjugateBasis

variable {rel} (B : ConjugateBasis rel)

/-- The exponent of each relator in the free conjugate basis, summing over its cosets. -/
noncomputable def exponents : Relations rel →* Multiplicative (FreeAbelianGroup I) :=
  (FreeGroup.lift (fun p : I × (F ⧸ Relations rel) ↦
    Multiplicative.ofAdd (FreeAbelianGroup.of p.1))).comp B.equiv.symm.toMonoidHom

@[simp] theorem exponents_of (i : I) (q : F ⧸ Relations rel) :
    B.exponents (B.equiv (FreeGroup.of (i, q))) =
      Multiplicative.ofAdd (FreeAbelianGroup.of i) := by
  simp [exponents]

/-- Ambient conjugation preserves the total exponent of each relator. -/
theorem exponents_conjugation (f : F) (n : Relations rel) :
    B.exponents (conjugation (Relations rel) f n) = B.exponents n := by
  have h : ((B.exponents.comp (conjugation (Relations rel) f)).comp B.equiv.toMonoidHom) =
      B.exponents.comp B.equiv.toMonoidHom := by
    apply FreeGroup.ext_hom
    rintro ⟨i, q⟩
    let q' := QuotientGroup.mk' (Relations rel) f * q
    let u := f * B.representative i q * (B.representative i q')⁻¹
    have hu : u ∈ Relations rel := by
      apply (QuotientGroup.eq_one_iff u).mp
      change QuotientGroup.mk' (Relations rel) u = 1
      simp only [u, map_mul, map_inv, B.representative_mk]
      simp [q']
    let v : Relations rel := ⟨u, hu⟩
    have hv : conjugation (Relations rel) f (B.equiv (FreeGroup.of (i, q))) =
        v * B.equiv (FreeGroup.of (i, q')) * v⁻¹ := by
      apply Subtype.ext
      change f * (B.equiv (FreeGroup.of (i, q))).val * f⁻¹ =
        u * (B.equiv (FreeGroup.of (i, q'))).val * u⁻¹
      rw [B.equiv_of, B.equiv_of]
      dsimp [u]
      group
    change B.exponents (conjugation (Relations rel) f (B.equiv (FreeGroup.of (i, q)))) =
      B.exponents (B.equiv (FreeGroup.of (i, q)))
    rw [hv, map_mul, map_mul, map_inv, B.exponents_of, B.exponents_of]
    simp [mul_comm]
  have hn := DFunLike.congr_fun h (B.equiv.symm n)
  simpa using hn

/-- The exponent homomorphism has the expected value on the original relators. -/
theorem exponents_relator (i : I) :
    B.exponents ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩ =
      Multiplicative.ofAdd (FreeAbelianGroup.of i) := by
  let r : Relations rel := ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩
  have hr : conjugation (Relations rel) (B.representative i 1) r =
      B.equiv (FreeGroup.of (i, 1)) := by
    apply Subtype.ext
    exact (B.equiv_of i 1).symm
  have h := B.exponents_conjugation (B.representative i 1) r
  rw [hr, B.exponents_of] at h
  exact h.symm

/-- A free conjugate basis gives an inverse to the canonical central relation coordinates. -/
noncomputable def inverseCoordinates : Additive (Kernel (Relations rel)) →+ FreeAbelianGroup I :=
  (liftInvariant (Relations rel) B.exponents B.exponents_conjugation).toAdditiveLeft

theorem inverseCoordinates_comp : B.inverseCoordinates.comp (coordinates rel) =
    AddMonoidHom.id (FreeAbelianGroup I) := by
  apply FreeAbelianGroup.lift_ext
  intro i
  change B.inverseCoordinates (coordinates rel (FreeAbelianGroup.of i)) = FreeAbelianGroup.of i
  rw [coordinates_of]
  change (liftInvariant (Relations rel) B.exponents B.exponents_conjugation
    (toCoinvariants (Relations rel) ⟨rel i, Subgroup.subset_normalClosure ⟨i, rfl⟩⟩)).toAdd = _
  rw [liftInvariant_toCoinvariants, B.exponents_relator]
  rfl

include B in
/-- The central relation coinvariants are freely generated by relators whenever their
normal closure admits a Cohen–Lyndon free conjugate basis. -/
theorem coordinates_bijective : Function.Bijective (coordinates rel) := by
  refine ⟨?_, coordinates_surjective rel⟩
  apply Function.LeftInverse.injective (g := B.inverseCoordinates)
  intro x
  exact DFunLike.congr_fun B.inverseCoordinates_comp x

end ConjugateBasis

end SmallPresentationStatements.RelationCoordinates
