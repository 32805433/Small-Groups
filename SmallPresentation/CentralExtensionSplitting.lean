module

public import SmallPresentation.KunnethTotal
public import SmallPresentation.HopfExact

/-! A central extension has no lifting obstruction once its Hopf obstruction
vanishes and the source abelianization is projective. The proof extends a
character of the relation group along a split exact sequence and uses it to
correct a free lift. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

section CharacterExtension

variable {A B C D : Type} [CommGroup A] [CommGroup B] [Group C] [Group D]

/-- A character on a kernel extends across a split abelian quotient, provided
it kills the kernel of the specified presentation of that kernel. -/
theorem extendCharacter_of_split (b : C →* B) (q : B →* A)
    (hexact : q.ker = b.range) (s : A →* B) (hs : q.comp s = MonoidHom.id A)
    (χ : C →* D) (hχ : b.ker ≤ χ.ker) :
    ∃ e : B →* D, e.comp b = χ := by
  let br : C →* b.range := b.rangeRestrict
  have hbr : Function.Surjective br := by
    rintro ⟨x,hx⟩
    obtain ⟨c,rfl⟩ := hx
    exact ⟨c,rfl⟩
  have hker : br.ker ≤ χ.ker := by
    intro c hc
    apply hχ
    exact congrArg Subtype.val hc
  let k : b.range →* D := br.liftOfSurjective hbr ⟨χ,hker⟩
  have hk (c : C) : k (br c) = χ c := by
    exact MonoidHom.liftOfRightInverse_comp_apply br (Function.surjInv hbr)
      (Function.rightInverse_surjInv hbr) ⟨χ,hker⟩ c
  let δ : B →* B := (MonoidHom.id B) / s.comp q
  have hδ (x : B) : δ x ∈ b.range := by
    rw [← hexact]
    change q (x / s (q x)) = 1
    rw [map_div, show q (s (q x)) = q x from DFunLike.congr_fun hs (q x)]
    simp
  let d : B →* b.range := δ.codRestrict _ hδ
  refine ⟨k.comp d, ?_⟩
  apply MonoidHom.ext
  intro c
  change k (d (b c)) = χ c
  have hbc : q (b c) = 1 := by
    change b c ∈ q.ker
    rw [hexact]
    exact ⟨c,rfl⟩
  have hd : d (b c) = br c := by
    apply Subtype.ext
    change b c / s (q (b c)) = b c
    rw [hbc,map_one,div_one]
  rw [hd,hk]

end CharacterExtension

variable (G : Type) [Group G]

noncomputable def canonicalQuotientEquiv : FreeGroup G ⧸ canonicalRelations G ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective (freeProjection G)
    (fun g ↦ ⟨FreeGroup.of g,FreeGroup.lift_apply_of⟩)

noncomputable def canonicalAbelianQuotient : Abelianization (FreeGroup G) →* Abelianization G :=
  (canonicalQuotientEquiv G).abelianizationCongr.toMonoidHom.comp
    (RelationExtension.abelianQuotient (canonicalRelations G))

theorem canonicalAbelianQuotient_ker :
    (canonicalAbelianQuotient G).ker = (RelationExtension.boundary (canonicalRelations G)).range := by
  rw [← RelationExtension.abelianQuotient_ker]
  apply Subgroup.ext
  intro x
  change (canonicalQuotientEquiv G).abelianizationCongr
    (RelationExtension.abelianQuotient (canonicalRelations G) x) = 1 ↔ _
  exact map_eq_one_iff _ (canonicalQuotientEquiv G).abelianizationCongr.injective

theorem canonicalAbelianQuotient_surjective : Function.Surjective (canonicalAbelianQuotient G) :=
  (canonicalQuotientEquiv G).abelianizationCongr.surjective.comp
    (RelationExtension.abelianQuotient_surjective (canonicalRelations G))

theorem canonicalAbelianQuotient_projection (x : CanonicalTotal G) :
    canonicalAbelianQuotient G (RelationExtension.abelianProjection (canonicalRelations G) x) =
      Abelianization.of (totalEvaluation G x) := by
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

variable {G} {E Q : Type} [Group E] [Group Q]

/-- A vanishing Hopf obstruction admits a lift whenever the abelianization
projection has a section. The lift agrees with the free lift on the derived
subgroup of the canonical central extension. -/
theorem centralLift_of_hopf_zero_of_split
    (s : Abelianization G →* Abelianization (FreeGroup G))
    (hs : (canonicalAbelianQuotient G).comp s = MonoidHom.id _)
    (π : E →* Q) (hc : UniversalCentralExtension.Central π) (f : G →* Q)
    (σ : CanonicalTotal G →* E) (hσ : π.comp σ = f.comp (totalEvaluation G))
    (hzero : ∀ x : Schur G, σ x.1.1 = 1) :
    ∃ l : G →* E, π.comp l = f ∧
      ∀ x : CanonicalTotal G, x ∈ commutator (CanonicalTotal G) →
        l (totalEvaluation G x) = σ x := by
  let N := canonicalRelations G
  let K := (π.ker).subgroupOf (Subgroup.center E)
  let : CommGroup K :=
    { (inferInstance : Group K) with
      mul_comm := fun x y ↦ by
        apply Subtype.ext
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp x.1.2 y.1.1).symm }
  have hnπ (n : RelationExtension.Kernel N) : π (σ n.1) = 1 := by
    rw [← MonoidHom.comp_apply, hσ]
    change f (totalEvaluation G n.1) = 1
    rw [(totalEvaluation_eq_one_iff G n.1).mpr n.2,map_one]
  let χ : RelationExtension.Kernel N →* K :=
    { toFun := fun n ↦ ⟨⟨σ n.1,hc (hnπ n)⟩,hnπ n⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one σ
      map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul σ x.1 y.1 }
  have hχ : (RelationExtension.boundary N).ker ≤ χ.ker := by
    intro n hn
    rw [hopf_exact] at hn
    obtain ⟨x,rfl⟩ := hn
    apply Subtype.ext
    apply Subtype.ext
    exact hzero x
  obtain ⟨e,he⟩ := extendCharacter_of_split (RelationExtension.boundary N)
    (canonicalAbelianQuotient G) (canonicalAbelianQuotient_ker G) s hs χ hχ
  let δ : CanonicalTotal G →* K :=
    e.comp (RelationExtension.abelianProjection N)
  have hδ (n : RelationExtension.Kernel N) : ((δ n.1).1 : E) = σ n.1 := by
    exact congrArg (fun z : K ↦ z.1.1) (DFunLike.congr_fun he n)
  let k : CanonicalTotal G →* E :=
    ((Subgroup.center E).subtype.comp K.subtype).comp δ⁻¹
  have hkcentral (x : CanonicalTotal G) (z : E) : Commute (k x) z := by
    change Commute (((δ x).1 : E)⁻¹) z
    exact (Subgroup.mem_center_iff.mp (δ x).1.2 z).symm |> Commute.inv_left
  let σ' : CanonicalTotal G →* E := MonoidHom.mk' (fun x ↦ σ x * k x) (by
    intro x y
    rw [map_mul,map_mul]
    exact ((hkcentral x (σ y)).mul_mul_mul_comm (σ x) (k y)).symm)
  have hkill : (totalEvaluation G).ker ≤ σ'.ker := by
    intro x hx
    have hn : x ∈ RelationExtension.Kernel N := (totalEvaluation_eq_one_iff G x).mp hx
    change σ x * ((δ x).1 : E)⁻¹ = 1
    rw [hδ ⟨x,hn⟩]
    exact mul_inv_cancel _
  let l : G →* E := (totalEvaluation G).liftOfRightInverse (totalGenerator G)
    (totalEvaluation_generator G) ⟨σ',hkill⟩
  have hl (x : CanonicalTotal G) : l (totalEvaluation G x) = σ' x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hkπ (x : CanonicalTotal G) : π (k x) = 1 := by
    change π (((δ x).1 : E)⁻¹) = 1
    rw [map_inv, show π ((δ x).1 : E) = 1 from (δ x).2,inv_one]
  refine ⟨l, ?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    rw [← totalEvaluation_generator G g, MonoidHom.comp_apply, hl]
    change π (σ (totalGenerator G g) * k (totalGenerator G g)) = f _
    rw [map_mul,hkπ,mul_one,← MonoidHom.comp_apply,hσ]
    rfl
  · intro x hx
    rw [hl]
    have hx' : RelationExtension.abelianProjection N x = 1 := by
      change x ∈ (RelationExtension.abelianProjection N).ker
      rw [RelationExtension.abelianProjection_ker]
      exact hx
    change σ x * ((e (RelationExtension.abelianProjection N x)).1 : E)⁻¹ = σ x
    rw [hx',map_one]
    simp

end SmallPresentationStatements.Homology
