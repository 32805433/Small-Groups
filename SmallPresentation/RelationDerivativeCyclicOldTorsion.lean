module

public import SmallPresentation.RelationDerivativeCyclicOld
public import SmallPresentation.CyclicModuleAdaptedCosets

/-! The finite-cyclic old relation summands are exact whenever the embedded factors
are torsion-free. All orbit coordinates and adapted representatives are constructed
internally; no choice of cosets is an additional hypothesis. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.FactorSplitting

variable {A I : Type} (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a) (new : I → FreeGroup (Σ a, X a))
  (φ : ∀ a, G a →* Quotient X G p new)
  (compat : ∀ a, (quotient X G p new).comp (FreeGroup.map (Sigma.mk a)) =
    (φ a).comp (p a))
  (hp : ∀ a, Function.Surjective (p a)) (hφ : ∀ a, Function.Injective (φ a))
  [htf : ∀ a, IsMulTorsionFree (G a)]
  (q : Quotient X G p new) (hq : IsOfFinOrder q) (n : ℕ) (hn : orderOf q = n + 1)
  (hperiod : oldAction X G p new q ^ (n + 1) = 1)

include compat hp hφ htf hq hn in
/-- Embedded torsion-free factors make the old relation complex exact in both
finite-cyclic parities; this holds for arbitrary factor presentations. -/
theorem oldAction_exact_of_torsionFree_factors :
    (CyclicModule.ofFiniteOrder (oldAction X G p new q) (n + 1) hperiod).EvenExact ∧
    (CyclicModule.ofFiniteOrder (oldAction X G p new q) (n + 1) hperiod).OddExact := by
  let B : A → Type := fun a ↦ DoubleCoset.Quotient
    (Subgroup.zpowers q : Set (Quotient X G p new)) (φ a).range
  let rep : ∀ a, B a × Fin (n + 1) → Quotient X G p new :=
    fun a ↦ CyclicModule.adaptedRepresentative (φ a).range q n
  have hb : ∀ a, Function.Bijective (fun z : (B a × Fin (n + 1)) × G a ↦
      rep a z.1 * φ a z.2) := fun a ↦
    (CyclicModule.adaptedCosetData (φ a) (hφ a) q hq n hn).bijective
  have hs : ∀ a b j, q * rep a (b, finRotate (n + 1) j) = rep a (b, j) :=
    fun a b j ↦ CyclicModule.adaptedRepresentative_step (φ a).range q n hn b j
  exact oldAction_exact X G p new φ compat B n rep hb q hs hp

include compat hp hφ htf hq hn in
/-- The even-exactness form used in the presentation torsion obstruction. -/
theorem oldAction_evenExact_of_torsionFree_factors :
    (CyclicModule.ofFiniteOrder (oldAction X G p new q) (n + 1) hperiod).EvenExact :=
  (oldAction_exact_of_torsionFree_factors X G p new φ compat hp hφ q hq n hn hperiod).1

end SmallPresentationStatements.RelationDerivative.FactorSplitting
