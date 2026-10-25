module

public import SmallPresentation.SignedCentralComparison

/-! The concrete signed relation kernel is free abelian on ordered-pair/code-type
indices. Its canonical basis and all normalized row coordinates are proved from
the generic relative-asphericity input and the checked centralization comparison. -/
@[expose] public section

namespace SmallPresentationStatements.SignedCoding.CentralComparison

open Word

variable {L d : ℕ} (Q : FP 2 L) (hC : CentrallyClosed Q.Group)

noncomputable def defect (a : Relative.Pair d) (j : Fin 2) : CentralGroup Q d :=
  (originalSource Q hC a (PresentedGroup.of j))⁻¹ * centralCode Q a.val.1 a.val.2 j

theorem defect_mem (a : Relative.Pair d) (j : Fin 2) :
    defect Q hC a j ∈ RelationExtension.Kernel (relationSubgroup Q d) := by
  change centralProjection Q d (defect Q hC a j) = 1
  simp only [defect, map_mul, map_inv, centralCode_projects Q a.val.1 a.val.2 a.property j]
  rw [show centralProjection Q d (originalSource Q hC a (PresentedGroup.of j)) =
    sourceHom Q a.val.1 a.val.2 a.property (PresentedGroup.of j)
    from DFunLike.congr_fun (originalSource_projects Q hC a) _]
  exact inv_mul_cancel _

noncomputable def defectElement (a : Relative.Pair d) (j : Fin 2) :
    RelationExtension.Kernel (relationSubgroup Q d) := ⟨defect Q hC a j, defect_mem Q hC a j⟩

theorem eval_originalVertex (w : Word d) : eval (originalVertex Q) w = originalMk Q (FreeGroup.mk w) := by
  have h : FreeGroup.lift (originalVertex Q (d := d)) = originalMk Q := by
    apply FreeGroup.ext_hom
    intro v
    rfl
  exact DFunLike.congr_fun h _

theorem relative_relator_to_defect (a : Relative.Pair d) (j : Fin 2) :
    fromRelative Q hC (relativeMk Q
      (RelativeSmallCancellation.relatorValue (Relative.FactorGroup Q) Relative.rowLength
        (Relative.rows Q) (a, j))) = defect Q hC a j := by
  rw [fromRelative_mk, Relative.relatorValue_literal, map_mul, map_inv,
    freeToOriginal_source, map_eval]
  simp only [freeToOriginal_vertex, eval_originalVertex]
  rfl

variable (hperfect : commutator Q.Group = ⊤) (hN : Noncyclic Q.Group)

noncomputable def basisEquiv : FreeAbelianGroup (Relative.Row d) ≃+
    Additive (RelationExtension.Kernel (relationSubgroup Q d)) :=
  (RelativeSmallCancellation.relationCoordinatesEquiv (Relative.FactorGroup Q)
    Relative.rowLength (Relative.rows Q) (Relative.rows_nontrivial Q hN)
    (Relative.rows_cyclically_reduced Q) (fun _ ↦ by change 19 ≤ 33; decide)
    (Relative.rows_triple_injective Q)).trans
      (kernelEquiv Q hC hperfect).symm.toAdditive

@[simp] theorem basisEquiv_of (a : Relative.Pair d) (j : Fin 2) :
    basisEquiv Q hC hperfect hN (FreeAbelianGroup.of (a, j)) =
      Additive.ofMul (defectElement Q hC a j) := by
  simp only [basisEquiv, AddEquiv.trans_apply, RelativeSmallCancellation.relationCoordinatesEquiv_of]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact relative_relator_to_defect Q hC a j

variable (hQ : Normalized Q)

include hQ in
theorem normalized_row_value (a : Relative.Pair d) (i : Fin L) :
    eval ![centralCode Q a.val.1 a.val.2 0, centralCode Q a.val.1 a.val.2 1] (Q.relator i) =
      (if i.val = 0 then defect Q hC a 0 else 1) * (if i.val = 1 then defect Q hC a 1 else 1) := by
  let f := originalSource Q hC a
  have hc (j : Fin 2) (x : CentralGroup Q d) : Commute (defect Q hC a j) x :=
    RelationExtension.kernel_central _ _ (defect_mem Q hC a j) x
  have hrows (i : Fin L) : eval ![f (PresentedGroup.of 0), f (PresentedGroup.of 1)] (Q.relator i) = 1 := by
    have heq : (![f (PresentedGroup.of 0), f (PresentedGroup.of 1)] : Fin 2 → CentralGroup Q d) =
        fun j ↦ f (PresentedGroup.of j) := by
      funext j
      fin_cases j <;> rfl
    rw [heq, ← map_eval, Q.eval_relator, map_one]
  have h := hQ.central_defect_row (f (PresentedGroup.of 0)) (f (PresentedGroup.of 1))
    (defect Q hC a 0) (defect Q hC a 1) (hc 0) (hc 1) hrows i
  simpa only [f, defect, mul_inv_cancel_left] using h

end SmallPresentationStatements.SignedCoding.CentralComparison
