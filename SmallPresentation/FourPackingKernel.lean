module

public import SmallPresentation.FourCentralTorsion
public import SmallPresentation.PackingRelationBasis
public import SmallPresentation.CentralGraphQuotient
public import SmallPresentation.FourCentralPermutation

/-! The four-row central orbit relations are integral bipartite edge sums. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral

open Word PackingBaseProduct

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

def centralRow (v w : ZMod (p ^ 2)) (i : Fin L) : C Q p :=
  mk Q p (PackingBase.row Q (Host.residue p) v w i)

theorem centralRow_eval (v w : ZMod (p ^ 2)) (i : Fin L) :
    centralRow Q p v w i =
      eval ![eval ![lamp Q p v,lamp Q p w] code₁,
        eval ![lamp Q p v,lamp Q p w] code₂] (Q.relator i) := by
  simp only [centralRow, PackingBase.row, PackingBase.map_pair_eval]
  rfl

theorem prod_ofFn_two {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n) (f : Fin n → G)
    (hf : ∀ i, 2 ≤ i.val → f i = 1) :
    (List.ofFn f).prod = f ⟨0,by omega⟩ * f ⟨1,by omega⟩ := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
      have hz : (List.ofFn (fun i : Fin n ↦ f i.succ.succ)).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact hf i.succ.succ (by simp)
      rw [hz, mul_one]
      rfl

variable (hp : p.Prime) (hC : CentrallyClosed Q.Group) (hQ : Normalized Q)

include hC hQ in
theorem centralRow_eq_one [NeZero p] (v w : ZMod (p ^ 2))
    (hπ : Host.residue p v = Host.residue p w) (hvw : v ≠ w)
    (i : Fin L) (hi : 2 ≤ i.val) : centralRow Q p v w i = 1 := by
  have h := globalRowElement_eq_one Q (Host.residue p) (Host.fiberEquiv p) hC hQ v w hπ hvw i hi
  exact congrArg Subtype.val h

include hp hC hQ in
theorem packed_eq_two [NeZero p] : packed Q p =
    centralRow Q p 0 (p : ZMod (p ^ 2)) (normalizedIndex Q hQ 0) *
      centralRow Q p 1 ((p+1 : ℕ) : ZMod (p ^ 2)) (normalizedIndex Q hQ 1) := by
  rw [packed, basePacked, map_list_prod, List.map_ofFn]
  change (List.ofFn (fun i : Fin L ↦ centralRow Q p (i.val : ZMod (p ^ 2))
    ((p+i.val : ℕ) : ZMod (p ^ 2)) i)).prod = _
  rw [prod_ofFn_two hQ.1 _ (fun i hi ↦ centralRow_eq_one Q p hC hQ _ _
    (FourPacking.slot_pair p hp i).2 (FourPacking.slot_pair p hp i).1 i hi)]
  simp only [Nat.cast_zero, Nat.add_zero, Nat.cast_one]
  rfl

variable (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

theorem action_centralRow (g : HostBS.Group) (σ : Equiv.Perm (ZMod (p ^ 2)))
    (hσ : ∀ v, action Q p u hu g (lamp Q p v) = lamp Q p (σ v))
    (v w : ZMod (p ^ 2)) (i : Fin L) :
    action Q p u hu g (centralRow Q p v w i) = centralRow Q p (σ v) (σ w) i := by
  rw [centralRow_eval, centralRow_eval]
  change (action Q p u hu g).toMonoidHom (eval _ _) = _
  simp only [PackingBase.map_pair_eval, MulEquiv.coe_toMonoidHom, hσ]

abbrev Vertices (p : ℕ) := BasisVertex (fun _ : ZMod p ↦ p)

noncomputable def basis [NeZero p] (hN : Noncyclic Q.Group) :
    FreeAbelianGroup (Vertices p ⊕ Vertices p) ≃+ Additive (RelationExtension.Kernel (N Q p)) :=
  sumBasisEquiv Q (Host.residue p) (Host.fiberEquiv p) hC hQ hN

theorem rows_edge [NeZero p] (hN : Noncyclic Q.Group)
    (v w v' w' : ZMod (p ^ 2))
    (hπ : Host.residue p v = Host.residue p w) (hvw : v ≠ w)
    (hπ' : Host.residue p v' = Host.residue p w') (hvw' : v' ≠ w') :
    centralRow Q p v w (normalizedIndex Q hQ 0) *
      centralRow Q p v' w' (normalizedIndex Q hQ 1) =
      CentralGraphQuotient.edgeElement (RelationExtension.Kernel (N Q p)) (basis Q p hC hQ hN)
        (pairVertex (Host.residue p) (Host.fiberEquiv p) v w hπ hvw)
        (pairVertex (Host.residue p) (Host.fiberEquiv p) v' w' hπ' hvw') := by
  unfold CentralGraphQuotient.edgeElement basis
  rw [map_add, sumBasisEquiv_of_left, sumBasisEquiv_of_right]
  rfl

include hp in
theorem orbit_edge_of_permutation [NeZero p] (hN : Noncyclic Q.Group)
    (g : HostBS.Group) (σ : Equiv.Perm (ZMod (p ^ 2)))
    (hσ : ∀ v w, Host.residue p (σ v) = Host.residue p (σ w) ↔
      Host.residue p v = Host.residue p w)
    (hlamp : ∀ v, action Q p u hu g (lamp Q p v) = lamp Q p (σ v)) :
    ∃ l r : Vertices p, action Q p u hu g (packed Q p) =
      CentralGraphQuotient.edgeElement (RelationExtension.Kernel (N Q p)) (basis Q p hC hQ hN) l r := by
  have h0 := FourPacking.slot_pair p hp (normalizedIndex Q hQ 0)
  have h1 := FourPacking.slot_pair p hp (normalizedIndex Q hQ 1)
  simp only [normalizedIndex, Fin.val_zero, Nat.cast_zero, Nat.add_zero] at h0
  simp only [normalizedIndex, Fin.val_one, Nat.cast_one] at h1
  have hπ0 := (hσ 0 (p : ZMod (p ^ 2))).mpr h0.2
  have hπ1 := (hσ 1 ((p+1 : ℕ) : ZMod (p ^ 2))).mpr h1.2
  have hn0 : σ 0 ≠ σ (p : ZMod (p ^ 2)) := fun h ↦ h0.1 (σ.injective h)
  have hn1 : σ 1 ≠ σ ((p+1 : ℕ) : ZMod (p ^ 2)) := fun h ↦ h1.1 (σ.injective h)
  refine ⟨pairVertex (Host.residue p) (Host.fiberEquiv p) _ _ hπ0 hn0,
    pairVertex (Host.residue p) (Host.fiberEquiv p) _ _ hπ1 hn1, ?_⟩
  rw [packed_eq_two Q p hp hC hQ, map_mul,
    action_centralRow Q p u hu g σ hlamp, action_centralRow Q p u hu g σ hlamp]
  exact rows_edge Q p hC hQ hN _ _ _ _ hπ0 hn0 hπ1 hn1

include hp hC hQ in
theorem remainingKernel_torsionFree_of_permutations [NeZero p] (hN : Noncyclic Q.Group)
    (hperm : ∀ g : HostBS.Group, ∃ σ : Equiv.Perm (ZMod (p ^ 2)),
      (∀ v w, Host.residue p (σ v) = Host.residue p (σ w) ↔ Host.residue p v = Host.residue p w) ∧
      ∀ v, action Q p u hu g (lamp Q p v) = lamp Q p (σ v)) :
    IsMulTorsionFree (RemainingKernel Q p u hu) := by
  apply CentralGraphQuotient.quotient_torsionFree_of_edges
    (RelationExtension.Kernel (N Q p)) (basis Q p hC hQ hN)
  · intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact (RelationExtension.kernel_central (N Q p) x hx y).symm
  · rintro _ ⟨g,rfl⟩
    obtain ⟨σ,hσ,hlamp⟩ := hperm g
    exact orbit_edge_of_permutation Q p hp hC hQ u hu hN g σ hσ hlamp

include hp hC hQ in
theorem remainingKernel_torsionFree (hN : Noncyclic Q.Group) :
    IsMulTorsionFree (RemainingKernel Q p u hu) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  exact remainingKernel_torsionFree_of_permutations Q p hp hC hQ u hu hN
    (action_permutation Q p u hu)

include hp hC hQ u hu in
theorem output_torsionFree_complete
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1)) (hL : L ≤ p)
    (hN : Noncyclic Q.Group) (hT : IsMulTorsionFree Q.Group) :
    IsMulTorsionFree (fourPresentation Q p).Group := by
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  exact output_torsionFree_of_kernel Q p hp u hu ho hL hN hT
    (remainingKernel_torsionFree Q p hp hC hQ u hu hN)

end SmallPresentationStatements.FourCentral
