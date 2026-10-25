module

public import SmallPresentation.CyclicModuleDirectSum

/-!
# The obstruction for decompositions into regular cyclic modules

This is the form used after restricting an induced relation-module decomposition
to a finite cyclic subgroup. All coefficient groups and index families are
arbitrary. The hypotheses specify the actual additive equivalences and their
compatibility with the norm and difference operators.
-/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule.Periodic

open DirectSum

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {I J K : Type*} {VA : I → Type*} {VB : J → Type*} {VC : K → Type*}
  [∀ i, AddCommGroup (VA i)] [∀ j, AddCommGroup (VB j)] [∀ k, AddCommGroup (VC k)]

/-- An exact four-term sequence ending in trivial integer coefficients cannot
have its three preceding terms equivariantly decomposed into regular modules
of a common cyclic order greater than one. -/
theorem integer_obstruction_of_regular_decompositions
    (n : ℕ) (hn : 0 < n) (PA : Periodic A) (PB : Periodic B) (PC : Periodic C)
    (i : A →+ B) (j : B →+ C) (p : C →+ ℤ)
    (hi : Function.Injective i) (hij : j.ker = i.range) (hjp : p.ker = j.range)
    (hp : Function.Surjective p)
    (hiC : Compatible PA PB i) (hjC : Compatible PB PC j)
    (hpC : Compatible PC (integer (n + 1)) p)
    (eA : (⨁ a, Fin (n + 1) → VA a) ≃+ A)
    (eB : (⨁ b, Fin (n + 1) → VB b) ≃+ B)
    (eC : (⨁ c, Fin (n + 1) → VC c) ≃+ C)
    (heA : Compatible (directSum (fun a ↦ regular (A := VA a) n)) PA
      eA.toAddMonoidHom)
    (heB : Compatible (directSum (fun b ↦ regular (A := VB b) n)) PB
      eB.toAddMonoidHom)
    (heC : Compatible (directSum (fun c ↦ regular (A := VC c) n)) PC
      eC.toAddMonoidHom) : False := by
  apply integer_obstruction (n + 1) (by omega) PA PB PC
    i j p hi hij hjp hp hiC hjC hpC
  · exact evenExact_of_equiv _ PA eA heA (regular_directSum_exact n).1
  · exact oddExact_of_equiv _ PB eB heB (regular_directSum_exact n).2
  · exact evenExact_of_equiv _ PC eC heC (regular_directSum_exact n).1

end SmallPresentationStatements.CyclicModule.Periodic
