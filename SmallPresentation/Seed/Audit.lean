module

import SmallPresentation.Seed
public meta import Lean

/-! The imported seed and its new adapters must be free of admissions. -/
open Lean Elab Command in
elab "#audit_seed " target:ident : command => do
  let name := target.getId
  unless ((← getEnv).find? name).isSome do
    throwError "Unknown seed checkpoint: {name}"
  let axioms ← Lean.collectAxioms name
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "{name} depends on unpermitted axiom {axiomName}"
  logInfo m!"{name}: {axioms}"

#audit_seed UniversalGroup.exists_two_generator_thirteen_relator_universal_group
#audit_seed SmallPresentationStatements.Seed.exists_two_thirteen_universal
#audit_seed SmallPresentationStatements.Seed.exists_universal_datum
#audit_seed SmallPresentationStatements.Seed.exists_two_thirteen_universal_with_abelianization
#audit_seed SmallPresentationStatements.Seed.seed_normalGenerator
#audit_seed SmallPresentationStatements.Seed.seed_abelianization
