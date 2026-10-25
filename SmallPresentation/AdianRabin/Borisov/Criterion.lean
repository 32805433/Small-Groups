module

/-
Ported from `GroupUndecidability/Borisov/Criterion.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.UniversalGroup.Simulator.Recognition.Core
public import SmallPresentation.AdianRabin.Borisov.Model.FinalModel

@[expose] public section

/-!
# Borisov's simulation criterion

The forward implication is the relator calculation in `Construction.lean`.  The
converse is the complete normal-form argument, culminating in the mod-five
free-product syllable comparison that bounds a coefficient preimage by one
displayed rule letter.
-/

namespace UniversalGroup
namespace Borisov

/-- The deep normal-form direction in Borisov's simulation theorem. -/
theorem criterion_converse
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (presentation datum).wordProblem (testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  BorisovFinalModel.criterion_converse_of_borisov_inputs datum
    (BorisovInputsBridge.rankFiveFree datum)
    (SimulatorRecognitionCore.baseIntersections datum)
    (SimulatorRecognitionCore.signed_recognition datum _) Q

/-- Borisov's simulation theorem, specialized to the standing datum. -/
theorem criterion
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P ↔
      (presentation datum).wordProblem (testWord Q) :=
  ⟨criterion_forward datum Q, criterion_converse datum Q⟩

end Borisov
end UniversalGroup
