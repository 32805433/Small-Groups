module

public import SmallPresentation.CyclicModuleDirectSum
public import Mathlib.RepresentationTheory.Basic

/-!
# Periodic operators of finite-group representations

This connects the elementary periodic obstruction to Mathlib's integer
representations and its actual finite-group norm. Equivariant additive maps
preserve both operators, so the obstruction applies to a relation sequence.
-/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open scoped BigOperators

universe u v w z

variable {G : Type u} [Group G] [Fintype G]
  {A : Type v} {B : Type w} {C : Type z}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Difference by a fixed group element and the full finite-group norm. -/
noncomputable def ofRepresentation (ρ : Representation ℤ G A) (g : G) : Periodic A where
  difference := (ρ g).toAddMonoidHom - AddMonoidHom.id A
  norm := ρ.norm.toAddMonoidHom
  difference_norm := by intro a; exact sub_eq_zero.mpr (ρ.self_norm_apply g a)
  norm_difference := by
    intro a
    change ρ.norm (ρ g a - a) = 0
    rw [map_sub, ρ.norm_self_apply, sub_self]

/-- Equivariance implies compatibility with the periodic operators. -/
theorem ofRepresentation_compatible
    (ρ : Representation ℤ G A) (σ : Representation ℤ G B) (g : G)
    (f : A →+ B) (hf : ∀ h a, f (ρ h a) = σ h (f a)) :
    Periodic.Compatible (ofRepresentation ρ g) (ofRepresentation σ g) f where
  difference := by
    intro a
    change f (ρ g a - a) = σ g (f a) - f a
    rw [map_sub, hf]
  norm := by
    intro a
    change f (ρ.norm a) = σ.norm (f a)
    simp only [Representation.norm, LinearMap.sum_apply, map_sum, hf]

/-- A map to trivial integer coefficients sends the norm to multiplication by
the group order, with the actual integer periodic complex as target. -/
theorem integer_compatible
    (ρ : Representation ℤ G A) (g : G) (p : A →+ ℤ)
    (hp : ∀ h a, p (ρ h a) = p a) :
    Periodic.Compatible (ofRepresentation ρ g) (Periodic.integer (Fintype.card G)) p where
  difference := by
    intro a
    change p (ρ g a - a) = 0
    rw [map_sub, hp, sub_self]
  norm := by
    intro a
    change p (ρ.norm a) = (Fintype.card G : ℤ) * p a
    simp [Representation.norm, LinearMap.sum_apply, map_sum, hp]

/-- A finite nontrivial subgroup is incompatible with an equivariant exact
relation sequence whose three periodic complexes have the indicated exactness. -/
theorem representation_obstruction
    (ρA : Representation ℤ G A) (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (g : G) (hcard : 1 < Fintype.card G)
    (i : A →+ B) (j : B →+ C) (p : C →+ ℤ)
    (hi : Function.Injective i) (hij : j.ker = i.range) (hjp : p.ker = j.range)
    (hp : Function.Surjective p)
    (hiρ : ∀ h a, i (ρA h a) = ρB h (i a))
    (hjρ : ∀ h b, j (ρB h b) = ρC h (j b))
    (hpρ : ∀ h c, p (ρC h c) = p c)
    (hA : (ofRepresentation ρA g).EvenExact)
    (hB : (ofRepresentation ρB g).OddExact)
    (hC : (ofRepresentation ρC g).EvenExact) : False :=
  Periodic.integer_obstruction (Fintype.card G) hcard
    (ofRepresentation ρA g) (ofRepresentation ρB g) (ofRepresentation ρC g)
    i j p hi hij hjp hp
    (ofRepresentation_compatible ρA ρB g i hiρ)
    (ofRepresentation_compatible ρB ρC g j hjρ)
    (integer_compatible ρC g p hpρ) hA hB hC

end SmallPresentationStatements.CyclicModule
