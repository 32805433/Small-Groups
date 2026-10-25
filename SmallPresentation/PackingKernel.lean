module

public import SmallPresentation.PackingAlgebra

/-!
# Isolating a stored row and the commutator-kernel inclusion

These lemmas prove the algebra used in both kernel-sandwich arguments. The
geometric input still needed in each application is that an affine conjugate
places the selected slot in the desired factor and every other slot outside it.
-/
@[expose] public section

namespace SmallPresentationStatements.PackingKernel

open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

/-- A product commuting with `x` forces any one factor to commute with `x`,
provided all the other factors do. The factors need not commute with one another. -/
theorem commute_of_stored_product {n : ℕ} (v : Fin n → G) (k : Fin n) (x : G)
    (htotal : Commute (List.ofFn v).prod x)
    (hother : ∀ j, j ≠ k → Commute (v j) x) : Commute (v k) x := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons] at htotal
    cases k using Fin.cases with
    | zero =>
      have htail : Commute (List.ofFn (fun j : Fin n ↦ v j.succ)).prod x := by
        apply Commute.list_prod_left
        intro z hz
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
        exact hother j.succ (Fin.succ_ne_zero j)
      simpa only [mul_inv_cancel_right] using htotal.mul_left htail.inv_left
    | succ k =>
      have hhead : Commute (v 0) x := hother 0 (Ne.symm (Fin.succ_ne_zero k))
      have htail : Commute (List.ofFn (fun j : Fin n ↦ v j.succ)).prod x := by
        simpa only [inv_mul_cancel_left] using hhead.inv_left.mul_left htotal
      apply ih (fun j ↦ v j.succ) k htail
      intro j hj
      exact hother j.succ (fun h ↦ hj (Fin.succ_injective n h))

/-- The centrality of the defining rows extends to their normal closure. -/
theorem normalClosure_maps_to_center (π : G →* H) (S : Set G)
    (hS : ∀ s ∈ S, π s ∈ Subgroup.center H) :
    Subgroup.normalClosure S ≤ (Subgroup.center H).comap π := by
  exact Subgroup.normalClosure_le_normal hS

/-- The lower kernel inclusion follows from centrality of all encoded rows. -/
theorem commutator_normalClosure_le_kernel (π : G →* H) (S : Set G)
    (hS : ∀ s ∈ S, π s ∈ Subgroup.center H) :
    ⁅Subgroup.normalClosure S, (⊤ : Subgroup G)⁆ ≤ π.ker := by
  rw [Subgroup.commutator_le]
  intro z hz x _
  change π ⁅z, x⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (normalClosure_maps_to_center π S hS hz) (π x)).symm

/-- Checking against a generating set suffices for the slot-isolation argument. -/
theorem central_of_commutes_generators (S : Set H) (hgen : Subgroup.closure S = ⊤)
    (z : H) (hz : ∀ x ∈ S, Commute z x) : z ∈ Subgroup.center H := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hcentralizer : Subgroup.closure S ≤ Subgroup.centralizer ({z} : Set H) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    change ∀ a ∈ ({z} : Set H), a * y = y * a
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact hz y hy
  have hx : x ∈ Subgroup.centralizer ({z} : Set H) := by
    apply hcentralizer
    rw [hgen]
    trivial
  exact (hx z (Set.mem_singleton z)).symm

end SmallPresentationStatements.PackingKernel
