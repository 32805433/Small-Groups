module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Normal generation and infinite cyclic abelianization

The homomorphism to the integers and the normal generator refer to the same group and element.
The equivalence below is constructed from explicit inverse homomorphisms.
-/
public section

namespace SmallPresentationStatements

variable {G : Type*} [Group G]

/-- Maps to an abelian group are determined by a normal generator. -/
theorem hom_ext_of_normalGenerator {A : Type*} [CommGroup A] (g : G)
    (hg : Subgroup.normalClosure ({g} : Set G) = ⊤) (f h : G →* A)
    (heq : f g = h g) : f = h := by
  have hker : Subgroup.normalClosure ({g} : Set G) ≤ (f * h⁻¹).ker := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simp [MonoidHom.mem_ker, heq]
  rw [hg] at hker
  ext x
  have hx := hker (show x ∈ (⊤ : Subgroup G) from trivial)
  simpa only [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply,
    mul_inv_eq_one] using hx

/-- Killing the chosen element gives the trivial quotient exactly when it normally generates. -/
theorem normalClosure_eq_top_of_quotient_subsingleton (g : G)
    (h : Subsingleton (G ⧸ Subgroup.normalClosure ({g} : Set G))) :
    Subgroup.normalClosure ({g} : Set G) = ⊤ := by
  apply top_unique
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (h.elim _ 1)

/-- To prove normal generation in a presentation, it suffices to kill every displayed generator
in the quotient by the proposed normal generator. -/
theorem presented_normalClosure_eq_top {α : Type*} (rels : Set (FreeGroup α))
    (g : PresentedGroup rels)
    (h : ∀ i : α,
      (QuotientGroup.mk (PresentedGroup.of (rels := rels) i) :
        PresentedGroup rels ⧸ Subgroup.normalClosure ({g} : Set (PresentedGroup rels))) = 1) :
    Subgroup.normalClosure ({g} : Set (PresentedGroup rels)) = ⊤ := by
  apply top_unique
  intro x _
  apply PresentedGroup.generated_by rels _ _ x
  intro i
  exact (QuotientGroup.eq_one_iff _).mp (h i)

/-- A normal generator with integer exponent one identifies the abelianization with `ℤ`. -/
def abelianizationEquivIntOfNormalGenerator (g : G)
    (hg : Subgroup.normalClosure ({g} : Set G) = ⊤)
    (f : G →* Multiplicative ℤ) (hf : f g = Multiplicative.ofAdd 1) :
    Abelianization G ≃* Multiplicative ℤ := by
  let forward : Abelianization G →* Multiplicative ℤ := Abelianization.lift f
  let backward : Multiplicative ℤ →* Abelianization G :=
    { toFun := fun z ↦ Abelianization.of g ^ z.toAdd
      map_one' := by simp
      map_mul' := by intro x y; simp [zpow_add] }
  have hback : backward.comp f = Abelianization.of := by
    apply hom_ext_of_normalGenerator g hg
    simp [backward, hf]
  have hleft : Function.LeftInverse backward forward := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a => exact DFunLike.congr_fun hback a
  have hright : Function.RightInverse backward forward := by
    intro z
    apply Multiplicative.toAdd.injective
    simp [forward, backward, hf]
  exact
    { forward with
      invFun := backward
      left_inv := hleft
      right_inv := hright }

theorem abelianization_Z_of_normalGenerator (g : G)
    (hg : Subgroup.normalClosure ({g} : Set G) = ⊤)
    (f : G →* Multiplicative ℤ) (hf : f g = Multiplicative.ofAdd 1) :
    Nonempty (Abelianization G ≃* Multiplicative ℤ) :=
  ⟨abelianizationEquivIntOfNormalGenerator g hg f hf⟩

end SmallPresentationStatements
