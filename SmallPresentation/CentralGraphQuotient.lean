module

public import SmallPresentation.BipartiteGraphKernel

/-! A central subgroup with an integral bipartite basis remains torsion-free
modulo the ambient normal closure of edge sums. The ambient normal closure
restricts to exactly the edge subgroup; no saturation hypothesis is assumed. -/
@[expose] public section

namespace SmallPresentationStatements.CentralGraphQuotient

variable {C P : Type} [Group C] (A : Subgroup C)
    (b : FreeAbelianGroup (P ⊕ P) ≃+ Additive A) (E : Set (P × P))

def edgeElement (l r : P) : C :=
  (Additive.toMul (b (FreeAbelianGroup.of (Sum.inl l) + FreeAbelianGroup.of (Sum.inr r)))).val

def edgeSet : Set C := {x | ∃ l r, (l,r) ∈ E ∧ x = edgeElement A b l r}

abbrev ambientRelations := Subgroup.normalClosure (edgeSet A b E)

def coordinateProjection : A →* Multiplicative (BipartiteGraphKernel.Group E) :=
  (BipartiteGraphKernel.projection E).toMultiplicative.comp b.symm.toMultiplicative.toMonoidHom

theorem coordinateProjection_edge (l r : P) (hlr : (l,r) ∈ E) :
    coordinateProjection A b E
      (Additive.toMul (b (FreeAbelianGroup.of (Sum.inl l) + FreeAbelianGroup.of (Sum.inr r)))) = 1 := by
  change BipartiteGraphKernel.projection E
    (b.symm (b (FreeAbelianGroup.of (Sum.inl l) + FreeAbelianGroup.of (Sum.inr r)))) = 0
  rw [b.symm_apply_apply, map_add]
  exact BipartiteGraphKernel.edge_eq_zero E l r hlr

variable (hc : A ≤ Subgroup.center C)

include hc in
theorem ambientRelations_le_mappedKernel :
    ambientRelations A b E ≤ (coordinateProjection A b E).ker.map A.subtype := by
  let K := (coordinateProjection A b E).ker.map A.subtype
  have hK : K ≤ Subgroup.center C := by
    rintro x ⟨a,ha,rfl⟩
    exact hc a.property
  let : K.Normal := Subgroup.normal_of_le_center hK
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨l,r,hlr,rfl⟩
  exact ⟨Additive.toMul (b (FreeAbelianGroup.of (Sum.inl l) + FreeAbelianGroup.of (Sum.inr r))),
    coordinateProjection_edge A b E l r hlr,rfl⟩

theorem kernel_le_restrictedRelations :
    (coordinateProjection A b E).ker ≤ (ambientRelations A b E).comap A.subtype := by
  let f : FreeAbelianGroup (P ⊕ P) →+ Additive C := A.subtype.toAdditive.comp b.toAddMonoidHom
  have hrel : BipartiteGraphKernel.relations E ≤
      (ambientRelations A b E).toAddSubgroup.comap f := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨l,r,hlr,rfl⟩
    change edgeElement A b l r ∈ ambientRelations A b E
    exact Subgroup.subset_normalClosure ⟨l,r,hlr,rfl⟩
  intro a ha
  have hz : b.symm (Additive.ofMul a) ∈ BipartiteGraphKernel.relations E := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    exact ha
  have h := hrel hz
  change (Additive.toMul (b (b.symm (Additive.ofMul a)))).val ∈ ambientRelations A b E at h
  rw [b.apply_symm_apply] at h
  change a.val ∈ ambientRelations A b E
  exact h

include hc in
theorem restrictedRelations_eq_kernel :
    (ambientRelations A b E).comap A.subtype = (coordinateProjection A b E).ker := by
  apply le_antisymm _ (kernel_le_restrictedRelations A b E)
  have h := Subgroup.comap_mono (f := A.subtype) (ambientRelations_le_mappedKernel A b E hc)
  simpa only [Subgroup.comap_map_eq_self_of_injective A.subtype_injective] using h

include hc in
theorem quotient_torsionFree : IsMulTorsionFree (A ⧸ (ambientRelations A b E).comap A.subtype) := by
  let := BipartiteGraphKernel.quotient_torsionFree E
  have hker := restrictedRelations_eq_kernel A b E hc
  let f := QuotientGroup.lift ((ambientRelations A b E).comap A.subtype)
    (coordinateProjection A b E) hker.le
  have hf : Function.Injective f := (QuotientGroup.injective_lift_iff _ _ _).mpr hker
  exact hf.isMulTorsionFree f

/-- If every imposed central relation is an edge sum, choose the graph of all
pairs realizing those relations. No explicit enumeration or uniqueness is needed. -/
theorem quotient_torsionFree_of_edges (hc : A ≤ Subgroup.center C)
    (S : Set C) (hS : ∀ x ∈ S, ∃ l r, x = edgeElement A b l r) :
    IsMulTorsionFree (A ⧸ (Subgroup.normalClosure S).comap A.subtype) := by
  let E : Set (P × P) := {lr | edgeElement A b lr.1 lr.2 ∈ S}
  have hE : edgeSet A b E = S := by
    ext x
    constructor
    · rintro ⟨l,r,h,rfl⟩
      exact h
    · intro hx
      obtain ⟨l,r,rfl⟩ := hS x hx
      exact ⟨l,r,hx,rfl⟩
  rw [← hE]
  exact quotient_torsionFree A b E hc

end SmallPresentationStatements.CentralGraphQuotient
