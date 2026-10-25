module

public import SmallPresentation.PermutationCycleCut
public import SmallPresentation.SmallCancellationGeometryComponents

/-!
# Cycle coordinates for corridor cuts

Every finite permutation cycle is explicitly coordinatized by its first-return period.
This supplies the interval coordinates required by the actual vertex-cut operation,
without assuming a planar realization or choosing an unverified cyclic ordering.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

attribute [local instance] Classical.propDecidable

variable {D : Type*} [Finite D] (σ : Equiv.Perm D) (a : D)

theorem orbit_period_pos : 0 < Function.minimalPeriod σ a :=
  Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts a)

/-- The actual iterate at each index below the first return, as a point of its cycle. -/
def orbitPoint (k : Fin (Function.minimalPeriod σ a)) : {d : D // σ.SameCycle a d} :=
  ⟨(σ ^ k.val) a, Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)⟩

theorem orbitPoint_bijective : Function.Bijective (orbitPoint σ a) := by
  constructor
  · intro i j h
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
    simpa only [orbitPoint, Equiv.Perm.coe_pow] using congrArg Subtype.val h
  · intro ⟨d, hd⟩
    obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
    refine ⟨⟨n % Function.minimalPeriod σ a, Nat.mod_lt _ (orbit_period_pos σ a)⟩, ?_⟩
    apply Subtype.ext
    change (σ ^ (n % Function.minimalPeriod σ a)) a = d
    calc
      _ = (σ ^ n) a := by
        simpa only [Equiv.Perm.coe_pow] using
          (Function.iterate_mod_minimalPeriod_eq (f := (σ : D → D)) (x := a) (n := n))
      _ = d := hn

noncomputable def orbitEquiv : Fin (Function.minimalPeriod σ a) ≃
    {d : D // σ.SameCycle a d} := Equiv.ofBijective _ (orbitPoint_bijective σ a)

@[simp] theorem orbitEquiv_val (k : Fin (Function.minimalPeriod σ a)) :
    (orbitEquiv σ a k).val = (σ ^ k.val) a := rfl

theorem orbitEquiv_rotate (k : Fin (Function.minimalPeriod σ a)) :
    (orbitEquiv σ a (finRotate _ k)).val = σ (orbitEquiv σ a k).val := by
  rw [orbitEquiv_val, orbitEquiv_val]
  have hv : (finRotate (Function.minimalPeriod σ a) k).val =
      (k.val + 1) % Function.minimalPeriod σ a := by
    rw [finRotate_apply]
    change (k.val + (1 % Function.minimalPeriod σ a)) % Function.minimalPeriod σ a = _
    exact Nat.add_mod_mod _ _ _
  rw [hv]
  have hh := Function.iterate_mod_minimalPeriod_eq (f := (σ : D → D)) (x := a)
    (n := k.val + 1)
  simpa only [Equiv.Perm.coe_pow, Function.iterate_succ_apply'] using hh

omit [Finite D] in
theorem orbit_invariant (d : D) : σ.SameCycle a (σ d) ↔ σ.SameCycle a d :=
  Equiv.Perm.sameCycle_apply_right

noncomputable def offOrbitPerm : Equiv.Perm {d : D // ¬σ.SameCycle a d} :=
  σ.subtypePerm (fun d ↦ not_congr (orbit_invariant σ a d))

/-- Split off one explicitly ordered cycle, retaining every other cycle unchanged. -/
noncomputable def orbitCoordinates :
    Fin (Function.minimalPeriod σ a) ⊕ {d : D // ¬σ.SameCycle a d} ≃ D :=
  (Equiv.sumCongr (orbitEquiv σ a) (Equiv.refl _)).trans
    (Equiv.sumCompl (σ.SameCycle a))

theorem orbitCoordinates_intertwines (d :
    Fin (Function.minimalPeriod σ a) ⊕ {d : D // ¬σ.SameCycle a d}) :
    orbitCoordinates σ a (Equiv.sumCongr (finRotate _) (offOrbitPerm σ a) d) =
      σ (orbitCoordinates σ a d) := by
  cases d with
  | inl k => exact orbitEquiv_rotate σ a k
  | inr k => rfl

theorem finRotate_finCongr {m n : ℕ} (h : m = n) (k : Fin m) :
    finCongr h (finRotate m k) = finRotate n (finCongr h k) := by
  subst n
  rfl

/-- Cutting at distinct points on the same actual cycle adds exactly one cycle. -/
theorem card_cutAt_of_sameCycle (b : D) (hne : a ≠ b) (hab : σ.SameCycle a b)
    [Fintype (Cycles σ)] [Fintype (Cycles (cutAt σ a b))] :
    Fintype.card (Cycles (cutAt σ a b)) = Fintype.card (Cycles σ) + 1 := by
  classical
  let k := (orbitEquiv σ a).symm ⟨b, hab⟩
  have hkb : (σ ^ k.val) a = b := by
    exact congrArg Subtype.val ((orbitEquiv σ a).apply_symm_apply ⟨b, hab⟩)
  have hk : 0 < k.val := by
    by_contra hh
    have hz : k.val = 0 := by omega
    exact hne (by simpa only [hz, pow_zero, Equiv.Perm.one_apply] using hkb)
  let m := k.val - 1
  let n := Function.minimalPeriod σ a - k.val - 1
  have hm : m + 1 = k.val := by dsimp [m]; omega
  have ht : (m + 1) + (n + 1) = Function.minimalPeriod σ a := by
    have hh := k.isLt
    dsimp [m, n]
    omega
  let e : Fin ((m + 1) + (n + 1)) ⊕ {d : D // ¬σ.SameCycle a d} ≃ D :=
    (Equiv.sumCongr (finCongr ht) (Equiv.refl _)).trans (orbitCoordinates σ a)
  have he (d : Fin ((m + 1) + (n + 1)) ⊕ {d : D // ¬σ.SameCycle a d}) :
      e (Equiv.sumCongr (finRotate _) (offOrbitPerm σ a) d) = σ (e d) := by
    cases d with
    | inl d =>
      change (orbitEquiv σ a (finCongr ht (finRotate _ d))).val =
        σ (orbitEquiv σ a (finCongr ht d)).val
      rw [finRotate_finCongr]
      exact orbitEquiv_rotate σ a _
    | inr d => rfl
  have hea : e (.inl (intervalStartLeft m n)) = a := by
    change (σ ^ 0) a = a
    simp
  have heb : e (.inl (intervalStartRight m n)) = b := by
    change (σ ^ (m + 1)) a = b
    rw [hm]
    exact hkb
  let := Fintype.ofFinite (Cycles (cutAt σ (e (.inl (intervalStartLeft m n)))
    (e (.inl (intervalStartRight m n)))))
  have hc := card_cutAt_of_intervalCoordinates σ (offOrbitPerm σ a) m n e he
  simpa only [hea, heb] using hc

omit [Finite D] in
/-- Before completing the old cycle, cutting toward a different cycle follows the old walk. -/
theorem cutAt_iterate_before_return (b : D) (hab : ¬σ.SameCycle a b) (j : ℕ)
    (hj : j < Function.minimalPeriod σ a) :
    (cutAt σ a b)^[j] a = σ^[j] a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
    rw [cutAt_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he
      have hp : Function.IsPeriodicPt σ (j + 1) a := by
        simpa only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply'] using he
      have hh := hp.minimalPeriod_le (by omega : 0 < j + 1)
      omega
    · intro he
      apply hab
      have h : σ.SameCycle a ((σ ^ (j + 1)) a) :=
        Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
      have hh : (σ ^ (j + 1)) a = b := by
        simpa only [Equiv.Perm.coe_pow, Function.iterate_succ_apply'] using he
      rwa [hh] at h

/-- A cut between different cycles connects the two marked points by an actual finite walk. -/
theorem cutAt_sameCycle_of_not_sameCycle (b : D) (hab : ¬σ.SameCycle a b) :
    (cutAt σ a b).SameCycle a b := by
  let N := Function.minimalPeriod σ a
  have hn : 0 < N := orbit_period_pos σ a
  have hr : (cutAt σ a b)^[N] a = b := by
    have hN : N = (N - 1) + 1 := by omega
    rw [hN, Function.iterate_succ_apply', cutAt_iterate_before_return σ a b hab _ (by omega)]
    rw [cutAt_apply]
    have hh : σ (σ^[N - 1] a) = a := by
      have hh₀ := Function.iterate_minimalPeriod (f := (σ : D → D)) (x := a)
      change σ^[N] a = a at hh₀
      rw [hN, Function.iterate_succ_apply'] at hh₀
      exact hh₀
    rw [hh, Equiv.swap_apply_left]
  refine ⟨(N : ℤ), ?_⟩
  simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hr

/-- Cutting between different cycles merges exactly those two cycles. -/
theorem card_cutAt_of_not_sameCycle (b : D) (hab : ¬σ.SameCycle a b)
    [Fintype (Cycles σ)] [Fintype (Cycles (cutAt σ a b))] :
    Fintype.card (Cycles σ) = Fintype.card (Cycles (cutAt σ a b)) + 1 := by
  have hn : a ≠ b := by rintro rfl; exact hab (.refl _ _)
  let := Fintype.ofFinite (Cycles (cutAt (cutAt σ a b) a b))
  have hc := card_cutAt_of_sameCycle (cutAt σ a b) a b hn
    (cutAt_sameCycle_of_not_sameCycle σ a b hab)
  simpa only [cutAt_cutAt] using hc

/-- Distinct points of one cycle lie in different cycles after cutting at those points. -/
theorem cutAt_not_sameCycle_of_sameCycle (b : D) (hne : a ≠ b)
    (hab : σ.SameCycle a b) : ¬(cutAt σ a b).SameCycle a b := by
  intro h
  let := Fintype.ofFinite (Cycles σ)
  let := Fintype.ofFinite (Cycles (cutAt σ a b))
  let := Fintype.ofFinite (Cycles (cutAt (cutAt σ a b) a b))
  have hc := card_cutAt_of_sameCycle σ a b hne hab
  have hd := card_cutAt_of_sameCycle (cutAt σ a b) a b hne h
  simp only [cutAt_cutAt] at hd
  omega

/-- The two cycle-count alternatives for every cut, with no coordinate hypotheses. -/
theorem card_cutAt_cases (b : D) (hne : a ≠ b)
    [Fintype (Cycles σ)] [Fintype (Cycles (cutAt σ a b))] :
    Fintype.card (Cycles (cutAt σ a b)) = Fintype.card (Cycles σ) + 1 ∨
      Fintype.card (Cycles σ) = Fintype.card (Cycles (cutAt σ a b)) + 1 := by
  classical
  by_cases h : σ.SameCycle a b
  · exact Or.inl (card_cutAt_of_sameCycle σ a b hne h)
  · exact Or.inr (card_cutAt_of_not_sameCycle σ a b h)

end SmallPresentationStatements.PermutationCycles
