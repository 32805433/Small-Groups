module

public import SmallPresentation.Basic
public import SmallPresentation.UniversalGroup.Foundations.Presentation

/-! # Definition-preserving conversion of the upstream presentation record -/
@[expose] public section

namespace SmallPresentationStatements.Seed

def fromUpstream {n m : ℕ} (P : UniversalGroup.FP n m) : FP n m := ⟨P.relator⟩

def toUpstream {n m : ℕ} (P : FP n m) : UniversalGroup.FP n m := ⟨P.relator⟩

theorem universal_fromUpstream {n m : ℕ} (P : UniversalGroup.FP n m)
    (hP : UniversalGroup.IsUniversal P.Group) : IsUniversal (fromUpstream P).Group := by
  intro a b Q
  exact hP a b (toUpstream Q)

end SmallPresentationStatements.Seed
