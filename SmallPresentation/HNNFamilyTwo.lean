module

public import SmallPresentation.HNNFamily
public import SmallPresentation.UniversalGroup.Foundations.HNN.Identifying

/-! Two successive identifying HNN extensions satisfy the arbitrary-family
presentation interface. This file proves the identification of all canonical
base maps and edge boundaries; it contains no homology admissions. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open UniversalGroup DirectSum

variable (G A B : Type) [Group G] [Group A] [Group B]
variable (l₁ r₁ : A →* G) (l₂ r₂ : B →* G)
variable (hl₁ : Function.Injective l₁) (hr₁ : Function.Injective r₁)
    (hl₂ : Function.Injective l₂) (hr₂ : Function.Injective r₂)

noncomputable abbrev TwoHNN :=
  IdentifyingHNN ((IdentifyingHNN.of l₁ r₁ hl₁ hr₁).comp l₂)
    ((IdentifyingHNN.of l₁ r₁ hl₁ hr₁).comp r₂)
    ((IdentifyingHNN.of_injective l₁ r₁ hl₁ hr₁).comp hl₂)
    ((IdentifyingHNN.of_injective l₁ r₁ hl₁ hr₁).comp hr₂)

noncomputable def twoBase : G →* TwoHNN G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂ :=
  (IdentifyingHNN.of _ _ _ _).comp (IdentifyingHNN.of l₁ r₁ hl₁ hr₁)

def edge₁ : H₁ A × H₁ B →+ H₁ G :=
  (map₁ l₁ - map₁ r₁).coprod (map₁ l₂ - map₁ r₂)

def edge₂ : H₂ A × H₂ B →+ H₂ G :=
  (map₂ l₁ - map₂ r₁).coprod (map₂ l₂ - map₂ r₂)

abbrev twoEdgeGroups : Bool → Type
  | false => A
  | true => B

@[reducible] instance twoEdgeGroups_group (b : Bool) : Group (twoEdgeGroups A B b) :=
  match b with
  | false => inferInstanceAs (Group A)
  | true => inferInstanceAs (Group B)

def twoLeft : ∀ b, twoEdgeGroups A B b →* G
  | false => l₁
  | true => l₂

def twoRight : ∀ b, twoEdgeGroups A B b →* G
  | false => r₁
  | true => r₂

noncomputable def twoStable : Bool → TwoHNN G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
  | false => IdentifyingHNN.of _ _ _ _ (IdentifyingHNN.stable l₁ r₁ hl₁ hr₁)
  | true => IdentifyingHNN.stable _ _ _ _

/-- The actual iterated HNN construction has the simultaneous two-edge universal property. -/
noncomputable def twoHNNPresentation :
    HNNFamilyPresentation (twoLeft G A B l₁ l₂) (twoRight G A B r₁ r₂)
      (TwoHNN G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂) where
  base := twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
  stable := twoStable G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
  conjugates := by
    intro b a
    cases b with
    | false =>
      let j : IdentifyingHNN l₁ r₁ hl₁ hr₁ →*
          TwoHNN G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂ := IdentifyingHNN.of _ _ _ _
      change (j (IdentifyingHNN.stable l₁ r₁ hl₁ hr₁))⁻¹ *
        j (IdentifyingHNN.of l₁ r₁ hl₁ hr₁ (l₁ a)) *
        j (IdentifyingHNN.stable l₁ r₁ hl₁ hr₁) =
          j (IdentifyingHNN.of l₁ r₁ hl₁ hr₁ (r₁ a))
      simpa only [map_mul, map_inv] using
        congrArg j (IdentifyingHNN.conjugates l₁ r₁ hl₁ hr₁ a)
    | true => exact IdentifyingHNN.conjugates _ _ _ _ a
  lift := fun f t h ↦
    IdentifyingHNN.lift _ _ _ _
      (IdentifyingHNN.lift l₁ r₁ hl₁ hr₁ f (t false) (h false)) (t true)
      (by
        intro b
        simp only [MonoidHom.comp_apply]
        exact h true b)
  lift_base := by
    intro H _ f t h g
    simp only [twoBase, MonoidHom.comp_apply, IdentifyingHNN.lift_of]
    exact IdentifyingHNN.lift_of l₁ r₁ hl₁ hr₁ f (t false) (h false) g
  lift_stable := by
    intro H _ f t h b
    cases b <;> simp only [twoStable, IdentifyingHNN.lift_of, IdentifyingHNN.lift_stable]
    exact IdentifyingHNN.lift_stable l₁ r₁ hl₁ hr₁ f (t false) (h false)
  hom_ext := by
    intro H _ f g hbase hstable
    apply IdentifyingHNN.hom_ext
    · intro x
      have heq : f.comp (IdentifyingHNN.of _ _ _ _) =
          g.comp (IdentifyingHNN.of _ _ _ _) := by
        apply IdentifyingHNN.hom_ext
        · exact hbase
        · exact hstable false
      exact DFunLike.congr_fun heq x
    · exact hstable true

include hl₁ hl₂ in
theorem twoLeft_injective (b : Bool) : Function.Injective (twoLeft G A B l₁ l₂ b) := by
  cases b
  · exact hl₁
  · exact hl₂

include hr₁ hr₂ in
theorem twoRight_injective (b : Bool) : Function.Injective (twoRight G A B r₁ r₂ b) := by
  cases b
  · exact hr₁
  · exact hr₂

/-- A two-term indexed direct sum is the binary product, with its canonical coordinates. -/
noncomputable def boolDirectSumEquiv (D : Bool → Type) [∀ b, AddCommGroup (D b)] :
    (⨁ b, D b) ≃+ D false × D true where
  toFun x := (x false, x true)
  invFun x := DirectSum.of D false x.1 + DirectSum.of D true x.2
  left_inv x := by
    apply DFinsupp.ext
    intro b
    cases b <;> simp [DirectSum.of_apply]
  right_inv x := by
    rcases x with ⟨x,y⟩
    simp [DirectSum.of_apply]
  map_add' _ _ := rfl

theorem two_boundary₁ :
    HNNFamilyPresentation.boundary₁
      (l := twoLeft G A B l₁ l₂) (r := twoRight G A B r₁ r₂) =
      (edge₁ G A B l₁ r₁ l₂ r₂).comp
        (boolDirectSumEquiv (fun b ↦ H₁ (twoEdgeGroups A B b))).toAddMonoidHom := by
  apply DirectSum.addHom_ext
  intro b x
  change HNNFamilyPresentation.boundary₁ _ = edge₁ G A B l₁ r₁ l₂ r₂
    ((DirectSum.of (fun b ↦ H₁ (twoEdgeGroups A B b)) b x) false,
      (DirectSum.of (fun b ↦ H₁ (twoEdgeGroups A B b)) b x) true)
  rw [HNNFamilyPresentation.boundary₁_of]
  cases b <;> simp [edge₁, twoLeft, twoRight, DirectSum.of_apply]

theorem two_boundary₂ :
    HNNFamilyPresentation.boundary₂
      (l := twoLeft G A B l₁ l₂) (r := twoRight G A B r₁ r₂) =
      (edge₂ G A B l₁ r₁ l₂ r₂).comp
        (boolDirectSumEquiv (fun b ↦ H₂ (twoEdgeGroups A B b))).toAddMonoidHom := by
  apply DirectSum.addHom_ext
  intro b x
  change HNNFamilyPresentation.boundary₂ _ = edge₂ G A B l₁ r₁ l₂ r₂
    ((DirectSum.of (fun b ↦ H₂ (twoEdgeGroups A B b)) b x) false,
      (DirectSum.of (fun b ↦ H₂ (twoEdgeGroups A B b)) b x) true)
  rw [HNNFamilyPresentation.boundary₂_of]
  cases b <;> simp [edge₂, twoLeft, twoRight, DirectSum.of_apply]

end SmallPresentationStatements.Homology
