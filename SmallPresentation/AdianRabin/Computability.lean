module

/-
Ported from `GroupUndecidability/Computability.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: Rewrite local import prefix; Convert to module/public-import/exposed-public-section format.
See `provenance/AdianRabin.json` for original and local source hashes.
-/

public import SmallPresentation.AdianRabin.Presentation
public import Mathlib.Computability.Reduce

@[expose] public section

namespace UniversalGroup

/-- A letterwise map from a finite alphabet is primitive recursive. -/
theorem list_map_primrec_of_finite
    {α β : Type*} [Primcodable α] [Primcodable β] [Finite α] (f : α → β) :
    Primrec (List.map f) :=
  Primrec.list_map Primrec.id ((Primrec.dom_finite f).comp₂ Primrec₂.right)

/-- Substituting a fixed word for each letter of a finite alphabet is primitive recursive. -/
theorem list_flatMap_primrec_of_finite
    {α β : Type*} [Primcodable α] [Primcodable β] [Finite α] (f : α → List β) :
    Primrec (List.flatMap f) :=
  Primrec.list_flatten.comp (list_map_primrec_of_finite f)

/-- Undecidability transfers forward along a computable many-one reduction. -/
theorem not_computablePred_of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop}
    (hp : ¬ ComputablePred p) (hred : p ≤₀ q) :
    ¬ ComputablePred q := by
  intro hq
  exact hp (ComputablePred.computable_of_manyOneReducible hred hq)

end UniversalGroup
