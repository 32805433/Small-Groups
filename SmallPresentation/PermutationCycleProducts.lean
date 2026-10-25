module

public import SmallPresentation.SmallCancellationGeometryBigonWords
public import SmallPresentation.SmallCancellationGeometryCorridorCycleCuts

/-!
# Noncommutative products on actual permutation cycles

Moving a cycle basepoint preserves the assertion that its ordered product is one.
Merging distinct cycles concatenates their complete ordered boundaries. These facts
retain the order of factors and apply to arbitrary groups.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D K : Type*}

theorem Walk.append {σ : Equiv.Perm D} {a b c : D} {l m : List D}
    (h : Walk σ a b l) (g : Walk σ b c m) : Walk σ a c (l ++ m) := by
  induction h with
  | nil => exact g
  | cons a b l h ih => exact .cons _ _ _ (ih g)

/-- A walk is unchanged if its outgoing permutation steps are unchanged. -/
theorem Walk.changePerm {σ τ : Equiv.Perm D} {a b : D} {l : List D}
    (h : Walk σ a b l) (he : ∀ d ∈ l, τ d = σ d) : Walk τ a b l := by
  induction h with
  | nil => exact .nil _
  | cons a b l h ih =>
    apply Walk.cons
    rw [he a (by simp)]
    exact ih (fun d hd ↦ he d (by simp [hd]))

variable [Finite D] (σ : Equiv.Perm D)

theorem cycleBoundary_ne_nil (a : D) : cycleBoundary σ a ≠ [] := by
  intro h
  have hm := mem_cycleBoundary_self σ a
  rw [h] at hm
  exact List.not_mem_nil hm

theorem cycleBoundary_cons (a : D) : ∃ l, cycleBoundary σ a = a :: l := by
  have hp := orbit_period_pos σ a
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [cycleBoundary, hn, List.ofFn_succ]
  exact ⟨_, rfl⟩

omit [Finite D] in
/-- Changing the marked start by one step rotates exactly one departure to the end. -/
theorem cycleBoundary_next (a : D) (l : List D) (he : cycleBoundary σ a = a :: l) :
    cycleBoundary σ (σ a) = l ++ [a] := by
  have hw := cycleBoundary_walk σ a
  rw [he] at hw
  cases hw with
  | cons _ _ _ ht =>
    symm
    apply (ht.append (.cons a _ [] (.nil _))).eq_cycleBoundary
    · simp
    · have hn := cycleBoundary_nodup σ a
      rw [he, List.nodup_cons] at hn
      apply List.nodup_append.mpr
      refine ⟨hn.2, by simp, ?_⟩
      intro d hd e he hde
      have heq : e = a := List.mem_singleton.mp he
      exact hn.1 ((hde.trans heq) ▸ hd)

variable [Group K] (w : D → K)

/-- Ordered multiplication around a based cycle. -/
noncomputable def cycleProduct (a : D) : K := ((cycleBoundary σ a).map w).prod

theorem cycleProduct_next_eq_one (a : D) :
    cycleProduct σ w (σ a) = 1 ↔ cycleProduct σ w a = 1 := by
  obtain ⟨l, hl⟩ := cycleBoundary_cons σ a
  simp only [cycleProduct, cycleBoundary_next σ a l hl, hl,
    List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]
  exact mul_eq_one_comm

/-- The assertion of trivial cycle product is independent of the marked incidence. -/
theorem cycleProduct_eq_one_of_sameCycle {a b : D} (h : σ.SameCycle a b) :
    cycleProduct σ w a = 1 ↔ cycleProduct σ w b = 1 := by
  have hh := constant_on_cycles σ (fun d ↦ cycleProduct σ w d = 1)
    (fun d ↦ propext (cycleProduct_next_eq_one σ w d)) h
  exact Iff.of_eq hh

/-- A whole old cycle becomes a walk to the other cycle's chosen start after a merge. -/
theorem cutAt_cycle_walk (a b : D) (hn : ¬σ.SameCycle a b) :
    Walk (cutAt σ a b) a b (cycleBoundary σ a) := by
  classical
  let n := Function.minimalPeriod σ a
  have hp : 0 < n := orbit_period_pos σ a
  have he : (cutAt σ a b)^[n] a = b := by
    have hn' : n = (n - 1) + 1 := by omega
    rw [hn', Function.iterate_succ_apply',
      cutAt_iterate_before_return σ a b hn _ (by omega), cutAt_apply]
    have hh : σ (σ^[n - 1] a) = a := by
      have hh := Function.iterate_minimalPeriod (f := (σ : D → D)) (x := a)
      change σ^[n] a = a at hh
      rwa [hn', Function.iterate_succ_apply'] at hh
    rw [hh, Equiv.swap_apply_left]
  have hw := Walk.of_iterate (cutAt σ a b) n a
  rw [he] at hw
  have hl : (List.ofFn (fun k : Fin n ↦ (cutAt σ a b)^[k.val] a)) =
      cycleBoundary σ a := by
    apply congrArg List.ofFn
    apply funext
    intro k
    exact cutAt_iterate_before_return σ a b hn k.val k.isLt
  rwa [hl] at hw

/-- Cutting between different cycles concatenates their actual complete based boundaries. -/
theorem cycleBoundary_cutAt_merge (a b : D) (hn : ¬σ.SameCycle a b) :
    cycleBoundary (cutAt σ a b) a = cycleBoundary σ a ++ cycleBoundary σ b := by
  have hw := cutAt_cycle_walk σ a b hn
  have hw' := cutAt_cycle_walk σ b a (fun hh ↦ hn hh.symm)
  have hcomm : cutAt σ b a = cutAt σ a b := by
    classical
    simp only [cutAt, Equiv.swap_comm b a]
  rw [hcomm] at hw'
  symm
  apply (hw.append hw').eq_cycleBoundary
  · intro he
    exact cycleBoundary_ne_nil σ a (List.append_eq_nil_iff.mp he).1
  · apply List.nodup_append.mpr
    refine ⟨cycleBoundary_nodup σ a, cycleBoundary_nodup σ b, ?_⟩
    intro d ha e hb hde
    subst e
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hb
    have hai : σ.SameCycle a d := by
      rw [← hi]
      exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
    have hbj : σ.SameCycle b d := by
      rw [← hj]
      exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
    exact hn (hai.trans hbj.symm)

/-- The corresponding exact product formula, without any commutativity assumption. -/
theorem cycleProduct_cutAt_merge (a b : D) (hn : ¬σ.SameCycle a b) :
    cycleProduct (cutAt σ a b) w a = cycleProduct σ w a * cycleProduct σ w b := by
  simp only [cycleProduct, cycleBoundary_cutAt_merge σ a b hn, List.map_append,
    List.prod_append]

/-- A cycle disjoint from the two splice points retains its exact departure list. -/
theorem cycleBoundary_cutAt_unchanged (a b d : D)
    (ha : ¬σ.SameCycle d a) (hb : ¬σ.SameCycle d b) :
    cycleBoundary (cutAt σ a b) d = cycleBoundary σ d := by
  classical
  symm
  apply ((cycleBoundary_walk σ d).changePerm ?_).eq_cycleBoundary
    (cycleBoundary_ne_nil σ d) (cycleBoundary_nodup σ d)
  intro e he
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
  rw [cutAt_apply]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro hh
    apply ha
    rw [← hh]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _))
  · intro hh
    apply hb
    rw [← hh]
    exact Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _))

theorem cycleProduct_cutAt_unchanged (a b d : D)
    (ha : ¬σ.SameCycle d a) (hb : ¬σ.SameCycle d b) :
    cycleProduct (cutAt σ a b) w d = cycleProduct σ w d := by
  simp only [cycleProduct, cycleBoundary_cutAt_unchanged σ a b d ha hb]

end SmallPresentationStatements.PermutationCycles
