module

public import SmallPresentation.ConversionClosed
public import SmallPresentation.MitosisLifting
public import SmallPresentation.DetectorAbelianization
public import SmallPresentation.Noncyclic
public import SmallPresentation.Extensions

/-!
# The literal source conversions after small-cancellation injection

All word counts, normalization, central closedness, lifting of the original seed,
noncyclicity and undecidability transfer are proved here. The remaining geometric
inputs are the perfectification embedding and, for the torsion-free branch,
torsion-freeness of the perfectification and of its central-extension kernel.
-/
@[expose] public section

namespace SmallPresentationStatements.Conversion

open Word

def perfectificationHom {k μ : ℕ} (T : FP k μ) : T.Group →* (perfectification T).Group :=
  presentationHom T
    (fun i ↦ eval (PresentedGroup.of (rels := (perfectification T).relSet)) (perfectCode i))
    (by
      intro i
      rw [← eval_subst]
      have h := (perfectification T).eval_relator (Fin.castAdd 2 i)
      simpa [perfectification, i.isLt] using h)

def doubled {n r : ℕ} (P : FP n r) :=
  MitosisWords.presentation (MitosisWords.presentation P)

def input {n r : ℕ} (P : FP n r) := normalizedPresentation (doubled P)

theorem input_normalized {n r : ℕ} (P : FP n r) : Normalized (input P) :=
  normalizedPresentation_normalized _

theorem input_centrallyClosed {n r : ℕ} (P : FP n r) : CentrallyClosed (input P).Group :=
  normalizedPresentation_centrallyClosed _

/-- The original seed, not merely a quotient of it, embeds in the actual normalized output. -/
theorem input_embedding {n r : ℕ} (P : FP n r)
    (hinj : Function.Injective (perfectificationHom (doubled P))) :
    ∃ f : P.Group →* (input P).Group, Function.Injective f := by
  obtain ⟨σ, hσ, _⟩ := MitosisLifting.finite_double_lift_injective P
    (normalizedProjection (doubled P)) (normalizedProjection_surjective _)
    ((UniversalCentralExtension.central_iff _).mpr (normalizedProjection_kernel_central _))
    (perfectificationHom (doubled P)) hinj
  exact ⟨σ, hσ⟩

def universalInput (P : FP 2 13) : FP 2 84 := input P

theorem universal_conversion_of_injective (P : FP 2 13)
    (hAb : Nonempty (Abelianization P.Group ≃* Multiplicative ℤ))
    (hinj : Function.Injective (perfectificationHom (doubled P))) :
    Normalized (universalInput P) ∧ CentrallyClosed (universalInput P).Group ∧
      Noncyclic (universalInput P).Group ∧
      ∃ f : P.Group →* (universalInput P).Group, Function.Injective f := by
  obtain ⟨f, hf⟩ := input_embedding P hinj
  obtain ⟨e⟩ := hAb
  exact ⟨input_normalized P, input_centrallyClosed P,
    (input_normalized P).noncyclic_of_nontrivial_embedding
      (not_subsingleton_of_abelianization_Z e) f hf, f, hf⟩

def torsionfreeInput (P : FP 2 13) : FP 2 216 := input (Detector.presentation P)

/-- The kernel and quotient torsion hypotheses are stated on their actual groups;
the normalized output's torsion-freeness is derived from them. -/
theorem input_torsionFree {n r : ℕ} (P : FP n r)
    (hbase : IsMulTorsionFree (perfectification (doubled P)).Group)
    (hker : IsMulTorsionFree (normalizedProjection (doubled P)).ker) :
    IsMulTorsionFree (input P).Group := by
  exact @torsionfree_of_kernel _ _ _ _ (normalizedProjection (doubled P)) hker hbase

theorem torsionfree_conversion_of_inputs (P : FP 2 13)
    (hW : ¬ ComputablePred P.wordProblem)
    (hinj : Function.Injective (perfectificationHom (doubled (Detector.presentation P))))
    (hbase : IsMulTorsionFree (perfectification (doubled (Detector.presentation P))).Group)
    (hker : IsMulTorsionFree (normalizedProjection (doubled (Detector.presentation P))).ker) :
    Normalized (torsionfreeInput P) ∧ CentrallyClosed (torsionfreeInput P).Group ∧
      Noncyclic (torsionfreeInput P).Group ∧ IsMulTorsionFree (torsionfreeInput P).Group ∧
      ¬ ComputablePred (torsionfreeInput P).wordProblem := by
  obtain ⟨f, hf⟩ := input_embedding (Detector.presentation P) hinj
  have hWP := FP.wordProblem_undecidable_of_injective f hf (Detector.wordProblem_undecidable P hW)
  exact ⟨input_normalized _, input_centrallyClosed _,
    (input_normalized _).noncyclic_of_undecidable hWP,
    input_torsionFree _ hbase hker, hWP⟩

end SmallPresentationStatements.Conversion
