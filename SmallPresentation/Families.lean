module

public import SmallPresentation.PackingConsequences
public import SmallPresentation.Gordon

/-! # Family assembly under explicit embedding and torsion hypotheses -/
public section

namespace SmallPresentationStatements

theorem not_subsingleton_of_undecidable {n m : ℕ} (P : FP n m)
    (hP : ¬ ComputablePred P.wordProblem) : ¬ Subsingleton P.Group := by
  intro hS
  apply hP
  have ht : ComputablePred (fun _ : Word n ↦ True) :=
    ⟨inferInstance, Computable.const true⟩
  apply ht.of_eq
  intro w
  exact ⟨fun _ ↦ Subsingleton.elim _ _, fun _ ↦ trivial⟩

namespace Gordon

theorem trivial_iff {m : ℕ} (P : FP 2 m)
    (hC : CyclicCollapse P) (hP : ¬ ComputablePred P.wordProblem)
    (hEmbed : ∀ w, ¬ P.wordProblem w →
      ∃ f : P.Group →* (presentation P w).Group, Function.Injective f)
    (w : Word 2) :
    (presentation P w).presentsTrivial ↔ P.wordProblem w := by
  refine ⟨?_, collapse P w hC⟩
  intro hT
  by_contra hw
  obtain ⟨f, hf⟩ := hEmbed w hw
  have : Subsingleton (presentation P w).Group := hT
  exact not_subsingleton_of_undecidable P hP ⟨fun x y ↦ hf (Subsingleton.elim _ _)⟩

theorem family_isAdianRabin {m : ℕ} (P : FP 2 m)
    (hC : CyclicCollapse P) (hP : ¬ ComputablePred P.wordProblem)
    (hEmbed : ∀ w, ¬ P.wordProblem w →
      ∃ f : P.Group →* (presentation P w).Group, Function.Injective f) :
    FP.IsAdianRabinFamily (fun j ↦ presentation P (wordOfNat 2 j)) :=
  FP.isAdianRabinFamily_of_wordProblem_reduction P (presentation P)
    (presentation_effective P) (trivial_iff P hC hP hEmbed) hP

theorem universal_of_nontrivial {m : ℕ} (P : FP 2 m)
    (hC : CyclicCollapse P) (hU : IsUniversal P.Group)
    (hEmbed : ∀ w, ¬ P.wordProblem w →
      ∃ f : P.Group →* (presentation P w).Group, Function.Injective f)
    (w : Word 2)
    (hT : ¬ (presentation P w).presentsTrivial) : IsUniversal (presentation P w).Group := by
  have hw : ¬ P.wordProblem w := fun hw ↦ hT (collapse P w hC hw)
  obtain ⟨f, hf⟩ := hEmbed w hw
  exact hU.of_injective f hf

theorem torsionfree {m : ℕ} (P : FP 2 m)
    (hC : CyclicCollapse P)
    (hPreserve : ∀ w, ¬ P.wordProblem w → IsMulTorsionFree (presentation P w).Group)
    (w : Word 2) :
    IsMulTorsionFree (presentation P w).Group := by
  by_cases hw : P.wordProblem w
  · have : Subsingleton (presentation P w).Group := collapse P w hC hw
    infer_instance
  · exact hPreserve w hw

end Gordon

theorem three_cyclicCollapse {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q) (p : ℕ) :
    Gordon.CyclicCollapse (threePresentation Q p) := by
  intro G _ z hz
  exact threePresentation_cyclic_collapse hQ p z 3 (hz 2)

theorem four_cyclicCollapse {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q) (p : ℕ) :
    Gordon.CyclicCollapse (fourPresentation Q p) := by
  intro G _ z hz
  exact fourPresentation_cyclic_collapse hQ p z 3 (hz 3)

end SmallPresentationStatements
