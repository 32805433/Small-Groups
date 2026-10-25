module

public import SmallPresentation.MitosisSchur
public import SmallPresentation.PerfectificationSchur

/-! Transport the actual normalized central kernel to its concrete Hopf kernel. -/
@[expose] public section

namespace SmallPresentationStatements.Conversion

variable {k μ : ℕ} (T : FP k μ)

def normalizedKernelToHopf : (normalizedProjection T).ker →*
    Homology.PresentationKernel (perfectificationRelations T) :=
  ((normalizedEquivRelationDerived T).toMonoidHom.comp (normalizedProjection T).ker.subtype).codRestrict _
    (fun z ↦ z.property)

theorem normalizedKernelToHopf_injective : Function.Injective (normalizedKernelToHopf T) := by
  intro x y h
  apply Subtype.ext
  apply (normalizedEquivRelationDerived T).injective
  exact congrArg Subtype.val h

theorem normalizedKernel_torsionFree_of_schur
    (h : IsMulTorsionFree (Homology.Schur (perfectification T).Group)) :
    IsMulTorsionFree (normalizedProjection T).ker := by
  let : IsMulTorsionFree (Homology.Schur (FreeGroup (Fin 2) ⧸ perfectificationRelations T)) := h
  obtain ⟨e⟩ := Homology.presentation_kernel_equiv (perfectificationRelations T)
  let : IsMulTorsionFree (Homology.PresentationKernel (perfectificationRelations T)) :=
    e.injective.isMulTorsionFree e.toMonoidHom
  exact (normalizedKernelToHopf_injective T).isMulTorsionFree (normalizedKernelToHopf T)

/-- The actual normalized conversion after two finite mitoses has torsion-free
central kernel. The original group needs no homology hypothesis. -/
theorem doubled_normalizedKernel_torsionFree {n r : ℕ} (P : FP n r) :
    IsMulTorsionFree (normalizedProjection (doubled P)).ker := by
  apply normalizedKernel_torsionFree_of_schur
  exact Relative.perfectification_schur_torsionFree (doubled P)
    (MitosisModel.finite_double_schur_torsionFree P)

end SmallPresentationStatements.Conversion
