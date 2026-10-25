module

public import SmallPresentation.CentralLifting
public import SmallPresentation.SignedCoding

/-! # The central relation extension `F/[N,F] → F/N` -/
@[expose] public section

namespace SmallPresentationStatements.RelationExtension

open scoped commutatorElement

variable {F : Type} [Group F] (N : Subgroup F) [N.Normal]

abbrev commutatorKernel : Subgroup F := ⁅N, (⊤ : Subgroup F)⁆

abbrev Total := F ⧸ commutatorKernel N

def projection : Total N →* F ⧸ N :=
  QuotientGroup.map _ N (MonoidHom.id F) (Subgroup.commutator_le_left N ⊤)

@[simp] theorem projection_mk (x : F) :
    projection N (QuotientGroup.mk' (commutatorKernel N) x) = QuotientGroup.mk' N x := rfl

theorem projection_surjective : Function.Surjective (projection N) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact ⟨QuotientGroup.mk' (commutatorKernel N) x, rfl⟩

theorem kernel_central :
    ∀ z ∈ (projection N).ker, ∀ x : Total N, z * x = x * z := by
  intro z hz x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutatorKernel N) z
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (commutatorKernel N) x
  have ha : a ∈ N := (QuotientGroup.eq_one_iff a).mp hz
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b)

/-- The central relation coinvariants, represented as the kernel of the projection. -/
abbrev Kernel := (projection N).ker

instance kernelCommGroup : CommGroup (Kernel N) where
  mul_comm x y := Subtype.ext (kernel_central N x.val x.property y.val)

/-- Every map from a centrally closed group lifts to the central relation extension. -/
theorem lift {Q : Type} [Group Q] (hQ : CentrallyClosed Q) (f : Q →* F ⧸ N) :
    ∃ σ : Q →* Total N, (projection N).comp σ = f :=
  hQ.lift (projection N) (projection_surjective N) (kernel_central N) f

end SmallPresentationStatements.RelationExtension

namespace SmallPresentationStatements.SignedCoding

variable {L d : ℕ}

abbrev relationSubgroup (Q : FP 2 L) (d : ℕ) := Subgroup.normalClosure (relators Q d)

abbrev CentralGroup (Q : FP 2 L) (d : ℕ) := RelationExtension.Total (relationSubgroup Q d)

/-- The exact `C_d → B_d` central extension of the manuscript. -/
def centralProjection (Q : FP 2 L) (d : ℕ) : CentralGroup Q d →* CodedGroup Q d :=
  RelationExtension.projection (relationSubgroup Q d)

def centralCode (Q : FP 2 L) (r u : Fin d) (j : Fin 2) : CentralGroup Q d :=
  QuotientGroup.mk' (RelationExtension.commutatorKernel (relationSubgroup Q d))
    (FreeGroup.mk (codeWord r u j))

theorem centralCode_projects (Q : FP 2 L) (r u : Fin d) (hru : r ≠ u) (j : Fin 2) :
    centralProjection Q d (centralCode Q r u j) =
      sourceHom Q r u hru (PresentedGroup.of j) := by
  rw [sourceHom, PresentedGroup.toGroup.of, eval_presented]
  rfl

/-- The concrete corrected signed-code words give an embedding into `C_d` once
the small-cancellation source map into `B_d` is known to be injective. -/
theorem corrected_source_embedding {Q : FP 2 L} (hQ : Normalized Q)
    (hC : CentrallyClosed Q.Group) (r u : Fin d) (hru : r ≠ u)
    (hinj : Function.Injective (sourceHom Q r u hru)) :
    ∃ σ : Q.Group →* CentralGroup Q d, Function.Injective σ ∧
      (centralProjection Q d).comp σ = sourceHom Q r u hru ∧
      σ (PresentedGroup.of 0) = centralCode Q r u 0 *
        (Word.eval ![centralCode Q r u 0, centralCode Q r u 1]
          (Q.relator ⟨0, lt_of_lt_of_le (by decide) hQ.1⟩))⁻¹ ∧
      σ (PresentedGroup.of 1) = centralCode Q r u 1 *
        (Word.eval ![centralCode Q r u 0, centralCode Q r u 1]
          (Q.relator ⟨1, lt_of_lt_of_le (by decide) hQ.1⟩))⁻¹ := by
  exact hQ.lift_corrected hC (centralProjection Q d)
    (RelationExtension.projection_surjective _) (RelationExtension.kernel_central _)
    (sourceHom Q r u hru) hinj (centralCode Q r u 0) (centralCode Q r u 1)
    (centralCode_projects Q r u hru 0) (centralCode_projects Q r u hru 1)

end SmallPresentationStatements.SignedCoding
