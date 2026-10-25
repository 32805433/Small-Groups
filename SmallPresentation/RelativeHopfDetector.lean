module

public import SmallPresentation.HopfNaturality
public import SmallPresentation.HopfExact
public import SmallPresentation.RelationCoordinates

/-!
# Natural Schur injection from an invariant relation detector

A conjugation-invariant detector on the target relation subgroup which recovers
source central relation classes proves injectivity of the actual induced Schur map.
This is the final algebraic interface used after a relative relation-module splitting.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology

open RelationExtension RelationCoordinates

variable {X Y : Type} (N : Subgroup (FreeGroup X)) (M : Subgroup (FreeGroup Y))
    [N.Normal] [M.Normal] (f : FreeGroup X →* FreeGroup Y) (hf : N ≤ M.comap f)

/-- The actual induced homomorphism of central relation coinvariants. -/
def centralRelationMap : Kernel N →* Kernel M :=
  ((totalMap N M f hf).comp (Kernel N).subtype).codRestrict (Kernel M) (by
    intro n
    change projection M (totalMap N M f hf n.val) = 1
    rw [totalMap_projection, show projection N n.val = 1 from n.property, map_one])

@[simp] theorem centralRelationMap_toCoinvariants (n : N) :
    centralRelationMap N M f hf (toCoinvariants N n) =
      toCoinvariants M ⟨f n.val, hf n.property⟩ := rfl

/-- A detector which recovers source relation classes splits their actual image. -/
theorem centralRelationMap_injective_of_detector
    (d : M →* Kernel N)
    (hinvariant : ∀ e n, d (conjugation M e n) = d n)
    (hrecover : ∀ n : N, d ⟨f n.val, hf n.property⟩ = toCoinvariants N n) :
    Function.Injective (centralRelationMap N M f hf) := by
  apply Function.LeftInverse.injective (g := liftInvariant M d hinvariant)
  intro z
  obtain ⟨n, rfl⟩ := toCoinvariants_surjective N z
  rw [centralRelationMap_toCoinvariants, liftInvariant_toCoinvariants, hrecover]

/-- The Hopf subgroup inclusion commutes with the central relation map. -/
theorem hopfInclusion_presentationMap (x : PresentationKernel N) :
    hopfInclusion M (presentationMap N M f hf x) =
      centralRelationMap N M f hf (hopfInclusion N x) := rfl

/-- A relation detector proves injectivity before changing the free presentations. -/
theorem presentationMap_injective_of_detector
    (d : M →* Kernel N)
    (hinvariant : ∀ e n, d (conjugation M e n) = d n)
    (hrecover : ∀ n : N, d ⟨f n.val, hf n.property⟩ = toCoinvariants N n) :
    Function.Injective (presentationMap N M f hf) := by
  intro x y heq
  apply hopfInclusion_injective N
  apply centralRelationMap_injective_of_detector N M f hf d hinvariant hrecover
  rw [← hopfInclusion_presentationMap, ← hopfInclusion_presentationMap, heq]

variable {B C : Type} [Group B] [Group C]

/-- The detector criterion identifies the homology map of the specified quotient homomorphism. -/
theorem schurMap_injective_of_relationDetector
    (p : FreeGroup X →* B) (q : FreeGroup Y →* C)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hpk : p.ker = N) (hqk : q.ker = M)
    (g : B →* C) (hcommute : q.comp f = g.comp p)
    (d : M →* Kernel N)
    (hinvariant : ∀ e n, d (conjugation M e n) = d n)
    (hrecover : ∀ n : N, d ⟨f n.val, hf n.property⟩ = toCoinvariants N n) :
    Function.Injective (schurMap g) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := (hopfEquivWithKernel N p hp hpk).surjective x
  obtain ⟨v, rfl⟩ := (hopfEquivWithKernel N p hp hpk).surjective y
  congr 1
  apply presentationMap_injective_of_detector N M f hf d hinvariant hrecover
  apply (hopfEquivWithKernel M q hq hqk).injective
  rw [hopfEquivWithKernel_natural N M p q hp hq hpk hqk f g hcommute hf,
    hopfEquivWithKernel_natural N M p q hp hq hpk hqk f g hcommute hf]
  exact hxy

/-- Additive formulation for the project's degree-two homology map. -/
theorem map₂_injective_of_relationDetector
    (p : FreeGroup X →* B) (q : FreeGroup Y →* C)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hpk : p.ker = N) (hqk : q.ker = M)
    (g : B →* C) (hcommute : q.comp f = g.comp p)
    (d : M →* Kernel N)
    (hinvariant : ∀ e n, d (conjugation M e n) = d n)
    (hrecover : ∀ n : N, d ⟨f n.val, hf n.property⟩ = toCoinvariants N n) :
    Function.Injective (map₂ g) :=
  schurMap_injective_of_relationDetector N M f hf p q hp hq hpk hqk g hcommute
    d hinvariant hrecover

end SmallPresentationStatements.Homology
