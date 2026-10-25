module

public import SmallPresentation.Seed.Abelianization
public import SmallPresentation.UndecidableSeed
public import SmallPresentation.GordonTorsion
public import SmallPresentation.AbsorbedKernel
public import SmallPresentation.PerfectificationConsequences
public import SmallPresentation.HomologyConversion
public import SmallPresentation.FourPackingKernel

/-!
# Structural assembly from the checked local constructions

The construction interfaces below assemble the proved conversion, packing, and
Gordon constructions. Their proof dependencies use only the standard Lean axioms.
See `formalization-status.json` for the verification inventory and upstream provenance.
-/
@[expose] public section

namespace SmallPresentationStatements

namespace StructuralObligations

/-- The literal seed's abelianization, discharged by the seventh-row calculation and
the explicit character in `Seed.Abelianization`. -/
theorem seed_abelianization (D : UniversalGroup.CodeWords) :
    Nonempty (Abelianization (Seed.fromUpstream
      (UniversalGroup.Embedding.thirteenPresentation D)).Group ≃* Multiplicative ℤ) := by
  exact Seed.seed_abelianization D

/-- The independent undecidable-word-problem input, discharged by the checked
seven-generator, fourteen-relator Borisov construction. -/
theorem exists_undecidable_word_problem :
    ∃ n m, ∃ P : FP n m, ¬ ComputablePred P.wordProblem := by
  exact UndecidableSeed.exists_undecidable_word_problem

/-- Universal conversion: two mitoses, perfectification, universal central extension,
and normalized presentation, including the actual embedding of the original seed. -/
theorem universal_conversion (P : FP 2 13) (_hP : IsUniversal P.Group)
    (hAb : Nonempty (Abelianization P.Group ≃* Multiplicative ℤ)) :
    ∃ Q : FP 2 84, Normalized Q ∧ CentrallyClosed Q.Group ∧ Noncyclic Q.Group ∧
      ∃ f : P.Group →* Q.Group, Function.Injective f := by
  exact ⟨Conversion.universalInput P, Conversion.universal_conversion_of_injective P hAb
    (Conversion.perfectificationHom_injective (Conversion.doubled P))⟩

/-- Torsion-free conversion: the five-generator detector HNN extension, its word reduction,
then the same conversion with the integral torsion-free kernel calculation. -/
theorem torsionfree_conversion (P : FP 2 13)
    (hP : ¬ ComputablePred P.wordProblem)
    (_hAb : Nonempty (Abelianization P.Group ≃* Multiplicative ℤ)) :
    ∃ Q : FP 2 216, Normalized Q ∧ CentrallyClosed Q.Group ∧ Noncyclic Q.Group ∧
      IsMulTorsionFree Q.Group ∧ ¬ ComputablePred Q.wordProblem := by
  have hdet : IsMulTorsionFree (Detector.presentation P).Group := Detector.torsionFree P
  have hm₁ : IsMulTorsionFree (MitosisWords.presentation (Detector.presentation P)).Group :=
    MitosisModel.presentation_torsionFree _
  have hm₂ : IsMulTorsionFree (Conversion.doubled (Detector.presentation P)).Group :=
    MitosisModel.presentation_torsionFree _
  exact ⟨Conversion.torsionfreeInput P, Conversion.torsionfree_conversion_of_inputs P hP
    (Conversion.perfectificationHom_injective _)
    (Conversion.perfectification_torsionFree _ hm₂)
    (Conversion.doubled_normalizedKernel_torsionFree _)⟩

/-- Three-row packing: signed-code injection, exact host, absorbed kernel sandwich and
central splitting, specialized to the certified modulus 101 and 84 stored rows. -/
theorem three_packing (Q : FP 2 84) (_hQ : Normalized Q)
    (hC : CentrallyClosed Q.Group) (hN : Noncyclic Q.Group) :
    ∃ f : Q.Group →* (threePresentation Q 101).Group, Function.Injective f := by
  have : Fact (1 < 101) := ⟨by decide⟩
  let u := Host.primitiveUnit 101 Arithmetic.prime_101 Arithmetic.order_101
  have hu : (u : ZMod (101 ^ 2)) = 2 :=
    Host.primitiveUnit_coe 101 Arithmetic.prime_101 Arithmetic.order_101
  exact AbsorbedPacking.source_embeds Q 101 Arithmetic.prime_101 (by decide) (by decide)
    Arithmetic.order_101 HostAlgebra.order_mod_101 u hu hC 0 1 (by decide)
    (SignedCoding.Relative.sourceHom_injective Q hN 0 1 (by decide))

/-- Four-row packing: signed-code injection, exact host and both packed kernel inclusions;
the integral free-abelian kernel calculation is required for the torsion assertion. -/
theorem four_packing (Q : FP 2 216) (hQ : Normalized Q)
    (hC : CentrallyClosed Q.Group) (hN : Noncyclic Q.Group)
    (hT : IsMulTorsionFree Q.Group) :
    (∃ f : Q.Group →* (fourPresentation Q 227).Group, Function.Injective f) ∧
      IsMulTorsionFree (fourPresentation Q 227).Group := by
  refine ⟨FourPacking.exists_embedding Q 227 Arithmetic.prime_227 Arithmetic.order_227
    (by decide) hC hN, ?_⟩
  let u := Host.primitiveUnit 227 Arithmetic.prime_227 Arithmetic.order_227
  have hu : (u : ZMod (227 ^ 2)) = 2 :=
    Host.primitiveUnit_coe 227 Arithmetic.prime_227 Arithmetic.order_227
  exact FourCentral.output_torsionFree_complete Q 227 Arithmetic.prime_227 hC hQ u hu
    Arithmetic.order_227 (by decide) hN hT

/-- The exact source embedding, discharged by the ported Gordon free-basis argument. -/
theorem gordon_injection {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w : Word 2) (hw : ¬ P.wordProblem w) :
    ∃ f : P.Group →* (Gordon.presentation P w).Group, Function.Injective f :=
  Gordon.exists_embedding P hAb w hw

/-- Gordon torsion preservation: identify the exact output with the free-basis amalgam and apply
the torsion theorem for amalgams. Injection alone does not establish this conclusion. -/
theorem gordon_torsionfree {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w : Word 2) (hw : ¬ P.wordProblem w) (hT : IsMulTorsionFree P.Group) :
    IsMulTorsionFree (Gordon.presentation P w).Group := by
  exact Gordon.torsionFree P hAb w hw hT

end StructuralObligations
end SmallPresentationStatements
