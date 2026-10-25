module

public import SmallPresentation.SmallCancellationGeometryRelativeRegions
public import SmallPresentation.SmallCancellationGeometryRelativeFaces

/-!
# First returns to retained incidences on coefficient-region boundaries

For an arbitrary permutation of a finite type, first return to any selected set is a genuine
permutation of that set. Its actual paths have no intermediate selected incidences and its
cycles are precisely the original cycles that meet the selected set. Applied to a coefficient
region's face permutation, this gives the ordered retained boundary incidence data.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

namespace FirstReturn

attribute [local instance] Classical.propDecidable

variable {D : Type*} [Finite D] (σ : Equiv.Perm D) (keep : D → Prop)

/-- Every selected incidence has a positive return, even if it is alone on its cycle. -/
theorem exists_time (d : {x // keep x}) : ∃ n : ℕ, 0 < n ∧ keep (σ^[n] d.val) := by
  refine ⟨Function.minimalPeriod σ d.val, ?_, ?_⟩
  · exact Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts d.val)
  · simpa only [Function.iterate_minimalPeriod] using d.property

noncomputable def time (d : {x // keep x}) : ℕ := Nat.find (exists_time σ keep d)

theorem time_pos (d : {x // keep x}) : 0 < time σ keep d := (Nat.find_spec (exists_time σ keep d)).1

theorem time_mem (d : {x // keep x}) : keep (σ^[time σ keep d] d.val) :=
  (Nat.find_spec (exists_time σ keep d)).2

theorem time_le (d : {x // keep x}) (n : ℕ) (hn : 0 < n) (hk : keep (σ^[n] d.val)) :
    time σ keep d ≤ n := Nat.find_min' (exists_time σ keep d) ⟨hn, hk⟩

theorem no_early (d : {x // keep x}) (n : ℕ) (hn : 0 < n) (hlt : n < time σ keep d) :
    ¬ keep (σ^[n] d.val) := fun h ↦ (Nat.not_le_of_gt hlt) (time_le σ keep d n hn h)

noncomputable def next (d : {x // keep x}) : {x // keep x} :=
  ⟨σ^[time σ keep d] d.val, time_mem σ keep d⟩

private theorem injective_of_le (d e : {x // keep x})
    (hle : time σ keep d ≤ time σ keep e) (heq : next σ keep d = next σ keep e) : d = e := by
  have hh := congrArg Subtype.val heq
  change σ^[time σ keep d] d.val = σ^[time σ keep e] e.val at hh
  have hm : time σ keep e = time σ keep d + (time σ keep e - time σ keep d) := by omega
  rw [hm, Function.iterate_add_apply] at hh
  have hd := (σ.injective.iterate (time σ keep d)) hh
  have ht : time σ keep e = time σ keep d := by
    by_contra hn
    have hp := time_pos σ keep d
    have hbad := no_early σ keep e (time σ keep e - time σ keep d) (by omega) (by omega)
    exact hbad (hd ▸ d.property)
  apply Subtype.ext
  simpa only [ht, Nat.sub_self, Function.iterate_zero_apply] using hd

theorem next_injective : Function.Injective (next σ keep) := by
  intro d e he
  rcases le_total (time σ keep d) (time σ keep e) with h | h
  · exact injective_of_le σ keep d e h he
  · exact (injective_of_le σ keep e d h he.symm).symm

/-- The actual first-return permutation, with no arbitrary reordering of selected incidences. -/
noncomputable def perm : Equiv.Perm {x // keep x} :=
  Equiv.ofBijective (next σ keep) (⟨next_injective σ keep, Finite.surjective_of_injective (next_injective σ keep)⟩)

@[simp] theorem perm_apply (d : {x // keep x}) : perm σ keep d = next σ keep d := rfl

/-- A first-return step follows the same original permutation cycle. -/
theorem sameCycle_next (d : {x // keep x}) : σ.SameCycle d.val (next σ keep d).val := by
  refine ⟨(time σ keep d : ℤ), ?_⟩
  simp only [zpow_natCast, Equiv.Perm.coe_pow]
  rfl

/-- The entire actual ordered path to the next retained boundary incidence. -/
theorem walk (d : {x // keep x}) :
    Walk σ d.val (next σ keep d).val
      (List.ofFn (fun k : Fin (time σ keep d) ↦ σ^[k.val] d.val)) :=
  Walk.of_iterate σ (time σ keep d) d.val

/-- First-return paths never traverse an original incidence twice. -/
theorem path_nodup (d : {x // keep x}) :
    (List.ofFn (fun k : Fin (time σ keep d) ↦ σ^[k.val] d.val)).Nodup := by
  have ht : time σ keep d ≤ Function.minimalPeriod σ d.val :=
    time_le σ keep d _
      (Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts d.val))
      (by simpa only [Function.iterate_minimalPeriod] using d.property)
  apply List.nodup_ofFn.mpr
  intro i j hh
  apply Fin.ext
  exact Function.iterate_injOn_Iio_minimalPeriod (lt_of_lt_of_le i.isLt ht)
    (lt_of_lt_of_le j.isLt ht) hh

/-- Every retained point encountered on an original forward walk is reached by a finite
number of actual first-return steps. -/
theorem iterate_reaches (n : ℕ) (d e : {x // keep x}) (h : σ^[n] d.val = e.val) :
    ∃ k : ℕ, (perm σ keep)^[k] d = e := by
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨0, Subtype.ext (by simpa only [hn, Function.iterate_zero_apply] using h)⟩
    · have hp := time_pos σ keep d
      have ht := time_le σ keep d n (by omega) (h ▸ e.property)
      have he : σ^[n - time σ keep d] (next σ keep d).val = e.val := by
        change σ^[n - time σ keep d] (σ^[time σ keep d] d.val) = e.val
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel ht]
        exact h
      obtain ⟨k, hk⟩ := ih (n - time σ keep d) (by omega) (next σ keep d) he
      exact ⟨k + 1, by simpa only [Function.iterate_succ_apply, perm_apply] using hk⟩

/-- First-return cycles retain exactly the original boundary-cycle membership. -/
theorem sameCycle_iff (d e : {x // keep x}) :
    (perm σ keep).SameCycle d e ↔ σ.SameCycle d.val e.val := by
  constructor
  · exact sameCycle_map_of_step (perm σ keep) σ Subtype.val (sameCycle_next σ keep)
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    obtain ⟨k, hk⟩ := iterate_reaches σ keep n d e (by simpa only [Equiv.Perm.coe_pow] using hn)
    exact ⟨(k : ℤ), by simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hk⟩

end FirstReturn
end SmallPresentationStatements.PermutationCycles

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D : Type*} [Finite D] (P : RibbonMap D) (old : D → Prop)
variable (hold : ∀ d, old (P.rotation d) ↔ old d)

/-- The actual cyclic order of retained coefficient leaves along every region boundary. -/
noncomputable def regionBoundary : Equiv.Perm {d // ¬old d} :=
  FirstReturn.perm (P.coefficientRegions old hold).face (fun d ↦ ¬old d)

/-- The retained boundary cycles are precisely the coefficient-region face cycles that
meet retained relator incidences. No disk or coefficient-equation assertion is implicit. -/
theorem regionBoundary_sameCycle_iff (d e : {d // ¬old d}) :
    (P.regionBoundary old hold).SameCycle d e ↔
      (P.coefficientRegions old hold).face.SameCycle d.val e.val :=
  FirstReturn.sameCycle_iff _ _ d e

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
