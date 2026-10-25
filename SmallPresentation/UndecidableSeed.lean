module

public import SmallPresentation.Basic
public import SmallPresentation.AdianRabin.Borisov.Criterion

/-!
# A checked finite presentation with undecidable word problem

The pinned Adian–Rabin development proves Borisov's simulation criterion from the
universal-machine halting problem. The existential needed here uses its seven-generator,
fourteen-relator presentation directly. The syntactic computability proof below adapts
`Host/Presentation.lean` at commit `fb4a401e8fbdba36e7b35c11fde2baa15592e185`,
without importing the subsequent host compression construction.
-/

@[expose] public section

namespace SmallPresentationStatements.UndecidableSeed

open UniversalGroup.Borisov

/-- Borisov's test-word map is computable purely as a map of finite lists. -/
theorem testWord_computable : Computable testWord := by
  have hpositive : Primrec positiveWord := by
    apply Primrec.of_eq
      (Primrec.list_flatMap Primrec.id
        ((Primrec.dom_finite
          (fun i : Fin 2 ↦ if i = 0 then s1Word else s2Word)).comp
            Primrec.snd).to₂)
    intro Q
    rfl
  have hletterInverse : Primrec fun x : SignedGenerator 7 ↦
      (x.1, !x.2) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  have hinverse : Primrec (@UniversalGroup.Word.inverse 7) := by
    apply Primrec.of_eq
      (Primrec.list_map Primrec.list_reverse
        (hletterInverse.comp Primrec.snd).to₂)
    intro w
    rfl
  have hconjugate : Primrec fun Q ↦
      UniversalGroup.Word.product
        [UniversalGroup.Word.inverse (positiveWord Q), tWord, positiveWord Q] := by
    apply Primrec.of_eq
      (Primrec.list_append.comp (hinverse.comp hpositive)
        (Primrec.list_append.comp (Primrec.const tWord) hpositive))
    intro Q
    simp [UniversalGroup.Word.product]
  have hcommutator : Primrec fun u : BorisovWord ↦
      UniversalGroup.Word.commutator u kWord := by
    apply Primrec.of_eq
      (Primrec.list_append.comp hinverse
        (Primrec.list_append.comp (Primrec.const (UniversalGroup.Word.inverse kWord))
          (Primrec.list_append.comp Primrec.id (Primrec.const kWord))))
    intro u
    rfl
  exact (hcommutator.comp hconjugate).to_comp

/-- The exact finite-presentation existential used by the small-presentation reductions. -/
theorem exists_undecidable_word_problem :
    ∃ (n m : ℕ) (P : FP n m), ¬ ComputablePred P.wordProblem := by
  obtain ⟨datum⟩ := UniversalGroup.Thue.exists_standingDatum
  let P : FP 7 14 := ⟨(presentation datum).relator⟩
  refine ⟨7, 14, P, ?_⟩
  apply UniversalGroup.not_computablePred_of_manyOneReducible datum.undecidable
  exact ⟨testWord, testWord_computable, criterion datum⟩

end SmallPresentationStatements.UndecidableSeed
