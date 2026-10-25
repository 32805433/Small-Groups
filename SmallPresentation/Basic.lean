module

public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Shared statement definitions

These definitions reproduce the contract in `SmallPresentationStatements.lean`.
This module deliberately does not import that file or its unfinished theorems.
-/
@[expose] public section

namespace SmallPresentationStatements

abbrev SignedGenerator (n : ℕ) := Fin n × Bool
abbrev Word (n : ℕ) := List (SignedGenerator n)

structure FP (n m : ℕ) where
  relator : Fin m → Word n

namespace FP

variable {n m : ℕ}

def relSet (P : FP n m) : Set (FreeGroup (Fin n)) :=
  Set.range fun i ↦ FreeGroup.mk (P.relator i)

abbrev Group (P : FP n m) := PresentedGroup P.relSet

def wordProblem (P : FP n m) (w : Word n) : Prop :=
  PresentedGroup.mk P.relSet (FreeGroup.mk w) = 1

def presentsTrivial (P : FP n m) : Prop :=
  Subsingleton P.Group

def Effective (A : ℕ → FP n m) : Prop :=
  Computable₂ fun j i ↦ (A j).relator i

def IsAdianRabinFamily (A : ℕ → FP n m) : Prop :=
  Effective A ∧ ¬ ComputablePred fun j ↦ (A j).presentsTrivial

end FP

def IsUniversal (G : Type*) [Group G] : Prop :=
  ∀ (n m : ℕ) (Q : FP n m),
    ∃ f : Q.Group →* G, Function.Injective f

def HasDisplayedNormalGenerator {n m : ℕ} (P : FP n m) : Prop :=
  ∃ k : Fin n,
    Subgroup.normalClosure
      ({PresentedGroup.of (rels := P.relSet) k} : Set P.Group) = ⊤

end SmallPresentationStatements
