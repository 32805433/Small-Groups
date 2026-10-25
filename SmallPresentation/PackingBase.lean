module

public import SmallPresentation.HostModel
public import SmallPresentation.SignedCoding

/-! The quotient of the partition product by all ordered-pair signed rows.
The normal subgroup and its quotient are literal; the permutation action descends. -/
@[expose] public section

namespace SmallPresentationStatements.PackingBase

open Word
variable {L : ℕ} (Q : FP 2 L) {V C : Type} (π : V → C)

def row (v w : V) (i : Fin L) : HostPartition.Group π :=
  eval ![eval ![HostPartition.generator π v, HostPartition.generator π w] code₁,
    eval ![HostPartition.generator π v, HostPartition.generator π w] code₂] (Q.relator i)

def rows : Set (HostPartition.Group π) :=
  {z | ∃ v w, π v = π w ∧ v ≠ w ∧ ∃ i, z = row Q π v w i}

def kernel : Subgroup (HostPartition.Group π) := Subgroup.normalClosure (rows Q π)

instance : (kernel Q π).Normal := Subgroup.normalClosure_normal

abbrev Group := HostPartition.Group π ⧸ kernel Q π

def quotient : HostPartition.Group π →* Group Q π := QuotientGroup.mk' _

theorem quotient_surjective : Function.Surjective (quotient Q π) := QuotientGroup.mk'_surjective _

theorem quotient_ker : (quotient Q π).ker = kernel Q π := QuotientGroup.ker_mk' _

def lamp (v : V) : Group Q π := quotient Q π (HostPartition.generator π v)

theorem quotient_row (v w : V) (hπ : π v = π w) (hvw : v ≠ w) (i : Fin L) :
    quotient Q π (row Q π v w i) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨v,w,hπ,hvw,i,rfl⟩)

variable (e : Equiv.Perm V) (he : ∀ v w, π (e v) = π (e w) ↔ π v = π w)

theorem map_pair_eval {A B : Type*} [_root_.Group A] [_root_.Group B]
    (f : A →* B) (a b : A) (w : Word 2) :
    f (eval ![a,b] w) = eval ![f a,f b] w := by
  rw [map_eval]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem lamp_row (v w : V) (hπ : π v = π w) (hvw : v ≠ w) (i : Fin L) :
    eval ![eval ![lamp Q π v,lamp Q π w] code₁,
      eval ![lamp Q π v,lamp Q π w] code₂] (Q.relator i) = 1 := by
  simpa only [row, map_pair_eval, lamp] using quotient_row Q π v w hπ hvw i

theorem lamps_commute (v w : V) (hπ : π v ≠ π w) :
    Commute (lamp Q π v) (lamp Q π w) :=
  (HostPartition.generators_commute π v w hπ).map (quotient Q π)

theorem perm_row (v w : V) (i : Fin L) :
    HostPartition.permMap π e he (row Q π v w i) = row Q π (e v) (e w) i := by
  simp only [row, map_pair_eval, HostPartition.permMap_generator]

theorem kernel_preserved : kernel Q π ≤ (kernel Q π).comap (HostPartition.permMap π e he) := by
  apply Subgroup.normalClosure_le_normal
  rintro z ⟨v,w,hπ,hvw,i,rfl⟩
  change HostPartition.permMap π e he (row Q π v w i) ∈ kernel Q π
  rw [perm_row]
  exact Subgroup.subset_normalClosure ⟨e v,e w,(he v w).mpr hπ,
    fun h ↦ hvw (e.injective h),i,rfl⟩

def permMap : Group Q π →* Group Q π :=
  QuotientGroup.map _ _ (HostPartition.permMap π e he) (kernel_preserved Q π e he)

@[simp] theorem permMap_quotient (x : HostPartition.Group π) :
    permMap Q π e he (quotient Q π x) = quotient Q π (HostPartition.permMap π e he x) := rfl

@[simp] theorem permMap_lamp (v : V) : permMap Q π e he (lamp Q π v) = lamp Q π (e v) := by
  simp [lamp]

theorem hom_ext {H : Type*} [_root_.Group H] {f g : Group Q π →* H}
    (h : ∀ v, f (lamp Q π v) = g (lamp Q π v)) : f = g := by
  have hc : f.comp (quotient Q π) = g.comp (quotient Q π) := by
    apply PresentedGroup.ext
    exact h
  apply MonoidHom.ext
  intro z
  obtain ⟨x,rfl⟩ := quotient_surjective Q π z
  exact DFunLike.congr_fun hc x

def permAut : MulAut (Group Q π) where
  toFun := permMap Q π e he
  invFun := permMap Q π e.symm (HostPartition.partition_symm π e he)
  left_inv x := by
    have h : (permMap Q π e.symm (HostPartition.partition_symm π e he)).comp
        (permMap Q π e he) = MonoidHom.id _ := by
      apply hom_ext Q π
      intro v
      simp
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (permMap Q π e he).comp
        (permMap Q π e.symm (HostPartition.partition_symm π e he)) = MonoidHom.id _ := by
      apply hom_ext Q π
      intro v
      simp
    exact DFunLike.congr_fun h x
  map_mul' := map_mul _

@[simp] theorem permAut_lamp (v : V) : permAut Q π e he (lamp Q π v) = lamp Q π (e v) :=
  permMap_lamp Q π e he v

@[simp] theorem permAut_inv_lamp (v : V) : (permAut Q π e he)⁻¹ (lamp Q π v) = lamp Q π (e.symm v) :=
  permMap_lamp Q π e.symm (HostPartition.partition_symm π e he) v

end SmallPresentationStatements.PackingBase
