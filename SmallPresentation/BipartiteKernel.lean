module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# The integral quotient of disjoint complete bipartite graphs

Each edge imposes the sum of its endpoints, with coefficient one. The resulting
quotient is explicitly free abelian on the component set. This is the integral
calculation in `Proofs.md`, not a rational rank computation.
-/
@[expose] public section

namespace SmallPresentationStatements.BipartiteKernel

open FreeAbelianGroup

variable (C L R : Type*)

abbrev Vertex := C × (L ⊕ R)

def relations : AddSubgroup (FreeAbelianGroup (Vertex C L R)) :=
  AddSubgroup.closure (Set.range fun e : C × L × R ↦
    of (e.1, Sum.inl e.2.1) + of (e.1, Sum.inr e.2.2))

abbrev Quotient := FreeAbelianGroup (Vertex C L R) ⧸ relations C L R

def projection : FreeAbelianGroup (Vertex C L R) →+ Quotient C L R :=
  QuotientAddGroup.mk' _

def signedSum : FreeAbelianGroup (Vertex C L R) →+ FreeAbelianGroup C :=
  lift fun v ↦ match v.2 with
    | Sum.inl _ => of v.1
    | Sum.inr _ => -of v.1

theorem relations_le_ker : relations C L R ≤ (signedSum C L R).ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro _ ⟨⟨c, l, r⟩, rfl⟩
  simp [signedSum, AddMonoidHom.mem_ker]

def componentMap : Quotient C L R →+ FreeAbelianGroup C :=
  QuotientAddGroup.lift _ (signedSum C L R) (relations_le_ker C L R)

theorem edge_eq_zero (c : C) (l : L) (r : R) :
    projection C L R (of (c, Sum.inl l)) +
      projection C L R (of (c, Sum.inr r)) = 0 := by
  rw [← map_add]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure ⟨(c, l, r), rfl⟩

theorem left_eq (c : C) (l l₀ : L) (r₀ : R) :
    projection C L R (of (c, Sum.inl l)) =
      projection C L R (of (c, Sum.inl l₀)) := by
  apply add_right_cancel (b := projection C L R (of (c, Sum.inr r₀)))
  rw [edge_eq_zero, edge_eq_zero]

theorem right_eq_neg (c : C) (l₀ : L) (r : R) :
    projection C L R (of (c, Sum.inr r)) =
      -projection C L R (of (c, Sum.inl l₀)) := by
  exact eq_neg_of_add_eq_zero_right (edge_eq_zero C L R c l₀ r)

/-- An explicit isomorphism: left vertices map to their component generator and
right vertices map to its negative. Nonempty sides are witnessed by `l₀,r₀`. -/
def quotientEquiv (l₀ : L) (r₀ : R) : Quotient C L R ≃+ FreeAbelianGroup C where
  toFun := componentMap C L R
  invFun := lift fun c ↦ projection C L R (of (c, Sum.inl l₀))
  left_inv := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H z =>
      change (lift fun c ↦ projection C L R (of (c, Sum.inl l₀)))
        (componentMap C L R (projection C L R z)) = projection C L R z
      induction z using FreeAbelianGroup.induction_on with
      | zero => simp [componentMap, projection]
      | of v =>
        rcases v with ⟨c, l | r⟩
        · exact (left_eq C L R c l l₀ r₀).symm
        · simpa [componentMap, signedSum, projection] using
            (right_eq_neg C L R c l₀ r).symm
      | neg z hz => simpa only [map_neg] using congrArg Neg.neg hz
      | add x y hx hy => simp only [map_add, hx, hy]
  right_inv := by
    intro z
    induction z using FreeAbelianGroup.induction_on with
    | zero => simp
    | of c => simp [componentMap, projection, signedSum]
    | neg z hz => simpa only [map_neg] using congrArg Neg.neg hz
    | add x y hx hy => simp only [map_add, hx, hy]
  map_add' := map_add _

/-- The integral quotient has no additive torsion. -/
theorem quotient_torsionFree (l₀ : L) (r₀ : R) : IsAddTorsionFree (Quotient C L R) := by
  let e := (quotientEquiv C L R l₀ r₀).trans (FreeAbelianGroup.equivFinsupp C)
  exact e.injective.isAddTorsionFree e.toAddMonoidHom

end SmallPresentationStatements.BipartiteKernel
