module

public import SmallPresentation.StructuralDefinitions
public import SmallPresentation.CentralDefects
public import SmallPresentation.Families

/-! # Noncyclicity of the normalized undecidable inputs -/
public section

namespace SmallPresentationStatements

theorem noncyclic_of_perfect_nontrivial {G : Type} [Group G]
    (hperfect : commutator G = ⊤) (hG : ¬ Subsingleton G) : Noncyclic G := by
  rintro ⟨g, hg⟩
  have hc : Subgroup.center G = ⊤ := by
    apply top_unique
    intro x _
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := hg x
    obtain ⟨b, rfl⟩ := hg y
    exact ((Commute.refl g).zpow_zpow b a).eq
  have hbot : commutator G = ⊥ := (commutator_eq_bot_iff_center_eq_top G).mpr hc
  have hall (x : G) : x = 1 := by
    have hx : x ∈ commutator G := by rw [hperfect]; trivial
    simpa only [hbot, Subgroup.mem_bot] using hx
  exact hG ⟨fun x y ↦ (hall x).trans (hall y).symm⟩

theorem Normalized.noncyclic_of_undecidable {L : ℕ} {Q : FP 2 L}
    (hQ : Normalized Q) (hW : ¬ ComputablePred Q.wordProblem) : Noncyclic Q.Group :=
  noncyclic_of_perfect_nontrivial hQ.commutator_eq_top (not_subsingleton_of_undecidable Q hW)

theorem Normalized.noncyclic_of_nontrivial_embedding {L : ℕ} {Q : FP 2 L}
    (hQ : Normalized Q) {P : Type} [Group P] (hP : ¬ Subsingleton P)
    (f : P →* Q.Group) (hf : Function.Injective f) : Noncyclic Q.Group := by
  apply noncyclic_of_perfect_nontrivial hQ.commutator_eq_top
  intro h
  exact hP ⟨fun x y ↦ hf (h.elim _ _)⟩

theorem not_subsingleton_of_abelianization_Z {P : Type} [Group P]
    (e : Abelianization P ≃* Multiplicative ℤ) : ¬ Subsingleton P := by
  intro h
  have : Subsingleton (Abelianization P) :=
    ⟨fun x y ↦ QuotientGroup.induction_on x fun a ↦
      QuotientGroup.induction_on y fun b ↦ congrArg Abelianization.of (h.elim a b)⟩
  have heq : (1 : Multiplicative ℤ) = Multiplicative.ofAdd (1 : ℤ) := by
    simpa using congrArg e (this.elim (e.symm 1) (e.symm (Multiplicative.ofAdd (1 : ℤ))))
  exact Int.zero_ne_one (congrArg Multiplicative.toAdd heq)

/-- An embedded undecidable source already proves the required noncyclicity. -/
theorem Normalized.noncyclic_of_embedding {L n m : ℕ} {Q : FP 2 L}
    (hQ : Normalized Q) (P : FP n m) (hW : ¬ ComputablePred P.wordProblem)
    (f : P.Group →* Q.Group) (hf : Function.Injective f) : Noncyclic Q.Group :=
  hQ.noncyclic_of_undecidable (FP.wordProblem_undecidable_of_injective f hf hW)

end SmallPresentationStatements
