module

public import SmallPresentation.FreeGroupCentralizerRoots

/-! Aperiodic cyclically reduced words are root-free. The proof records the literal
period forced by a proper power, so it can be applied to metric row certificates. -/
@[expose] public section

namespace SmallPresentationStatements.FreeGroupCentralizer

open FreeGroup

variable {X : Type*}

/-- A cyclically reduced word cannot retain a nonempty conjugating prefix. -/
theorem cyclicallyReduced_conjugator_nil (u v : List (X × Bool))
    (h : IsCyclicallyReduced (u ++ v ++ invRev u)) : u = [] := by
  cases u with
  | nil => rfl
  | cons a u =>
    have hh : IsCyclicallyReduced (a :: (u ++ v ++ invRev u) ++ [(a.1, !a.2)]) := by
      simpa only [invRev, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append] using h
    have hn := (isCyclicallyReduced_cons_append_iff.mp hh).2 rfl
    cases a.2 <;> simp_all

/-- A positive power whose reduced word is cyclically reduced is a literal repetition
of the cyclic reduction of the root. -/
theorem cyclicallyReduced_power_word [DecidableEq X] (w : FreeGroup X) (n : ℕ)
    (hn : n ≠ 0) (hcyclic : IsCyclicallyReduced (w ^ n).toWord) :
    (w ^ n).toWord = (List.replicate n (reduceCyclically w.toWord)).flatten := by
  have he : (w ^ n).toWord = reduceCyclically.conjugator w.toWord ++
      (List.replicate n (reduceCyclically w.toWord)).flatten ++
      invRev (reduceCyclically.conjugator w.toWord) := by
    rw [toWord_pow, reduceCyclically.reduce_flatten_replicate isReduced_toWord n, ite_eq_right hn]
  have hu := cyclicallyReduced_conjugator_nil (reduceCyclically.conjugator w.toWord)
    (List.replicate n (reduceCyclically w.toWord)).flatten (he ▸ hcyclic)
  simpa only [hu, List.nil_append, invRev, List.reverse_nil, List.map_nil, List.append_nil] using he

/-- Rotating a concatenation of repeated blocks by one block fixes it. -/
theorem rotate_flatten_replicate {Y : Type*} (v : List Y) (n : ℕ) :
    (List.replicate n v).flatten.rotate v.length = (List.replicate n v).flatten := by
  cases n with
  | zero => simp
  | succ n =>
    have he : v ++ (List.replicate n v).flatten = (List.replicate n v).flatten ++ v := by
      calc
        v ++ (List.replicate n v).flatten = (List.replicate (n + 1) v).flatten := by
          rw [List.replicate_succ, List.flatten_cons]
        _ = (List.replicate n v).flatten ++ v := by
          rw [List.replicate_succ', List.flatten_append]
          simp
    rw [List.replicate_succ, List.flatten_cons, List.rotate_append_length_eq]
    exact he.symm

/-- No nonzero rotation shorter than the word fixes it. -/
def RotationAperiodic {Y : Type*} (v : List Y) : Prop :=
  ∀ k : ℕ, 0 < k → k < v.length → v.rotate k ≠ v

/-- An aperiodic, nonempty cyclically reduced word represents a root-free free-group element. -/
theorem rootFree_of_cyclicallyReduced_aperiodic (v : List (X × Bool))
    (hcyclic : IsCyclicallyReduced v) (hne : v ≠ []) (hperiod : RotationAperiodic v) :
    RootFree (FreeGroup.mk v) := by
  classical
  intro w n hpow
  have hv : (FreeGroup.mk v).toWord = v := by
    rw [toWord_mk, hcyclic.isReduced.reduce_eq]
  have hn : n ≠ 0 := by
    intro hn0
    have he := congrArg FreeGroup.toWord hpow
    rw [hn0, pow_zero, toWord_one, hv] at he
    exact hne he.symm
  have hc : IsCyclicallyReduced (w ^ n).toWord := by rwa [hpow, hv]
  have he : v = (List.replicate n (reduceCyclically w.toWord)).flatten := by
    simpa only [hpow, hv] using cyclicallyReduced_power_word w n hn hc
  let k := (reduceCyclically w.toWord).length
  have hlen : v.length = n * k := by simp [he, k]
  have hk : 0 < k := by
    have hvpos := List.length_pos_iff.mpr hne
    rw [hlen] at hvpos
    exact Nat.pos_of_mul_pos_left hvpos
  by_contra hnot
  have htwo : 2 ≤ n := by omega
  have hlt : k < v.length := by
    rw [hlen]
    have hm := Nat.mul_le_mul_right k htwo
    omega
  apply hperiod k hk hlt
  rw [he]
  exact rotate_flatten_replicate _ n

end SmallPresentationStatements.FreeGroupCentralizer
