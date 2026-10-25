module

public import SmallPresentation.BipartiteKernel

/-! # Integral quotients for arbitrary bipartite graphs

Edge sums have coefficient one at both endpoints. Negating the right side
identifies this quotient with the free abelian group on connected components.
The graph may be infinite, disconnected, or have isolated vertices.
-/
@[expose] public section

namespace SmallPresentationStatements.BipartiteGraphKernel
open FreeAbelianGroup

variable {L R : Type*} (E : Set (L × R))

def edgeRelation (x y : L ⊕ R) : Prop :=
  ∃ l r, (l,r) ∈ E ∧ x = Sum.inl l ∧ y = Sum.inr r

abbrev Component := Quot (edgeRelation E)

def relations : AddSubgroup (FreeAbelianGroup (L ⊕ R)) :=
  AddSubgroup.closure {x | ∃ l r, (l,r) ∈ E ∧ x = of (Sum.inl l) + of (Sum.inr r)}

abbrev Group := FreeAbelianGroup (L ⊕ R) ⧸ relations E

def projection : FreeAbelianGroup (L ⊕ R) →+ Group E := QuotientAddGroup.mk' _

theorem edge_eq_zero (l : L) (r : R) (h : (l,r) ∈ E) :
    projection E (of (Sum.inl l)) + projection E (of (Sum.inr r)) = 0 := by
  rw [← map_add]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure ⟨l,r,h,rfl⟩

def coordinate : L ⊕ R → FreeAbelianGroup (Component E)
  | .inl l => of (Quot.mk _ (Sum.inl l))
  | .inr r => -of (Quot.mk _ (Sum.inr r))

def signedSum : FreeAbelianGroup (L ⊕ R) →+ FreeAbelianGroup (Component E) :=
  lift (coordinate E)

theorem relations_le_ker : relations E ≤ (signedSum E).ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro x ⟨l,r,h,rfl⟩
  have heq : (Quot.mk _ (Sum.inl l) : Component E) = Quot.mk _ (Sum.inr r) :=
    Quot.sound ⟨l,r,h,rfl,rfl⟩
  simp [AddMonoidHom.mem_ker, signedSum, coordinate, heq]

def forward : Group E →+ FreeAbelianGroup (Component E) :=
  QuotientAddGroup.lift _ (signedSum E) (relations_le_ker E)

def signedVertex : L ⊕ R → Group E
  | .inl l => projection E (of (Sum.inl l))
  | .inr r => -projection E (of (Sum.inr r))

def componentVertex : Component E → Group E :=
  Quot.lift (signedVertex E) (by
    rintro x y ⟨l,r,h,rfl,rfl⟩
    exact eq_neg_of_add_eq_zero_left (edge_eq_zero E l r h))

def backward : FreeAbelianGroup (Component E) →+ Group E := lift (componentVertex E)

theorem backward_forward : (backward E).comp (forward E) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H z =>
    change backward E (forward E (projection E z)) = projection E z
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp
    | of v => cases v <;> simp [forward, signedSum, coordinate, backward,
        componentVertex, signedVertex, projection]
    | neg z hz => simpa only [map_neg] using congrArg Neg.neg hz
    | add x y hx hy => simp only [map_add, hx, hy]

theorem forward_backward : (forward E).comp (backward E) = AddMonoidHom.id _ := by
  apply FreeAbelianGroup.lift_ext
  intro c
  induction c using Quot.ind with
  | mk v => cases v <;> simp [forward, backward, signedSum, coordinate,
      componentVertex, signedVertex, projection]

/-- The integral graph quotient, including all isolated components. -/
def quotientEquiv : Group E ≃+ FreeAbelianGroup (Component E) where
  toFun := forward E
  invFun := backward E
  left_inv := DFunLike.congr_fun (backward_forward E)
  right_inv := DFunLike.congr_fun (forward_backward E)
  map_add' := map_add _

theorem quotient_torsionFree : IsAddTorsionFree (Group E) := by
  let e := (quotientEquiv E).trans (FreeAbelianGroup.equivFinsupp (Component E))
  exact e.injective.isAddTorsionFree e.toAddMonoidHom

end SmallPresentationStatements.BipartiteGraphKernel
