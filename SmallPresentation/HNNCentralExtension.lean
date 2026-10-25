module

public import SmallPresentation.HNNFamily

/-!
# Transporting central extensions through HNN presentations

An extension of a vertex group extends through a family of HNN identifications
when the two pullbacks to each edge are identified over that edge and on the
central kernel. The proof below uses universal properties and centrality only;
injectivity of the new vertex map can be supplied separately by HNN normal forms.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology

open UniversalCentralExtension

variable {I G K E L : Type} {A B : I → Type}
  [Group G] [Group K] [Group E] [Group L] [∀ i, Group (A i)] [∀ i, Group (B i)]
variable {l r : ∀ i, A i →* G} {l' r' : ∀ i, B i →* E}

/-- Compatible quotient maps between vertex and edge groups of two HNN presentations. -/
structure HNNFamilyQuotient (P : HNNFamilyPresentation l r K)
    (T : HNNFamilyPresentation l' r' L) where
  vertex : E →* G
  edge : ∀ i, B i →* A i
  left : ∀ i, vertex.comp (l' i) = (l i).comp (edge i)
  right : ∀ i, vertex.comp (r' i) = (r i).comp (edge i)

namespace HNNFamilyQuotient

variable {P : HNNFamilyPresentation l r K} {T : HNNFamilyPresentation l' r' L}
variable (D : HNNFamilyQuotient P T)

/-- The induced homomorphism sends stable letters to their corresponding stable letters. -/
noncomputable def map : L →* K :=
  T.lift (P.base.comp D.vertex) P.stable (by
    intro i b
    change (P.stable i)⁻¹ * P.base (D.vertex (l' i b)) * P.stable i =
      P.base (D.vertex (r' i b))
    rw [show D.vertex (l' i b) = l i (D.edge i b) from DFunLike.congr_fun (D.left i) b,
      show D.vertex (r' i b) = r i (D.edge i b) from DFunLike.congr_fun (D.right i) b]
    exact P.conjugates i _)

@[simp] theorem map_base (e : E) : D.map (T.base e) = P.base (D.vertex e) :=
  T.lift_base _ _ _ e

@[simp] theorem map_stable (i : I) : D.map (T.stable i) = P.stable i :=
  T.lift_stable _ _ _ i

/-- The image of the old central kernel in the new vertex group. -/
def kernelImage : Subgroup L := D.vertex.ker.map T.base

variable (hc : Central D.vertex)
variable (hkernel : ∀ (i : I) (z : D.vertex.ker), ∃ b : B i, l' i b = z ∧ r' i b = z)

include hc hkernel in
theorem kernelImage_central : D.kernelImage ≤ Subgroup.center L := by
  rintro _ ⟨z, hz, rfl⟩
  have hconj : (MulAut.conj (T.base z)).toMonoidHom = MonoidHom.id L := by
    apply T.hom_ext
    · intro e
      change T.base z * T.base e * (T.base z)⁻¹ = T.base e
      have hze := (central_iff D.vertex).mp hc z hz e
      have h := congrArg T.base hze
      simp only [map_mul] at h
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    · intro i
      obtain ⟨b, hleft, hright⟩ := hkernel i ⟨z, hz⟩
      have h := T.conjugates i b
      rw [hleft, hright] at h
      have hzst : T.base z * T.stable i = T.stable i * T.base z := by
        have hh := congrArg (fun x : L ↦ T.stable i * x) h
        simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
      change T.base z * T.stable i * (T.base z)⁻¹ = T.stable i
      rw [hzst, mul_assoc, mul_inv_cancel, mul_one]
  apply Subgroup.mem_center_iff.mpr
  intro x
  have h := DFunLike.congr_fun hconj x
  change T.base z * x * (T.base z)⁻¹ = x at h
  have hh := congrArg (fun y : L ↦ y * T.base z) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm

include hc hkernel in
theorem kernelImage_normal : D.kernelImage.Normal :=
  Subgroup.normal_of_le_center (D.kernelImage_central hc hkernel)

theorem kernelImage_le_ker : D.kernelImage ≤ D.map.ker := by
  rintro _ ⟨z, hz, rfl⟩
  change D.map (T.base z) = 1
  rw [D.map_base, show D.vertex z = 1 from hz, map_one]

variable (hvertex : Function.Surjective D.vertex) (hedge : ∀ i, Function.Surjective (D.edge i))

include hc hkernel hvertex hedge in
/-- Quotienting by the old central kernel recovers the original HNN presentation. -/
theorem map_ker_and_surjective : D.map.ker = D.kernelImage ∧ Function.Surjective D.map := by
  let := D.kernelImage_normal hc hkernel
  let q := QuotientGroup.mk' D.kernelImage
  let v : G →* L ⧸ D.kernelImage := D.vertex.liftOfSurjective hvertex
    ⟨q.comp T.base, by
      intro z hz
      change q (T.base z) = 1
      exact (QuotientGroup.eq_one_iff _).mpr ⟨z, hz, rfl⟩⟩
  have hvcomp : v.comp D.vertex = q.comp T.base := MonoidHom.liftOfRightInverse_comp ..
  have hv (e : E) : v (D.vertex e) = q (T.base e) := DFunLike.congr_fun hvcomp e
  have hrel : ∀ i a, (q (T.stable i))⁻¹ * v (l i a) * q (T.stable i) = v (r i a) := by
    intro i a
    obtain ⟨b, rfl⟩ := hedge i a
    rw [← show D.vertex (l' i b) = l i (D.edge i b) from DFunLike.congr_fun (D.left i) b,
      ← show D.vertex (r' i b) = r i (D.edge i b) from DFunLike.congr_fun (D.right i) b,
      hv, hv]
    simpa only [map_mul, map_inv] using congrArg q (T.conjugates i b)
  let back := P.lift v (fun i ↦ q (T.stable i)) hrel
  let forward : L ⧸ D.kernelImage →* K := QuotientGroup.lift _ D.map D.kernelImage_le_ker
  have hforward (x : L) : forward (q x) = D.map x := rfl
  have hback_map : back.comp D.map = q := by
    apply T.hom_ext
    · intro e
      change back (D.map (T.base e)) = q (T.base e)
      rw [D.map_base, show back (P.base (D.vertex e)) = v (D.vertex e) from P.lift_base _ _ _ _]
      exact hv e
    · intro i
      change back (D.map (T.stable i)) = q (T.stable i)
      rw [D.map_stable]
      exact P.lift_stable _ _ _ i
  have hforward_back : forward.comp back = MonoidHom.id K := by
    apply P.hom_ext
    · intro g
      obtain ⟨e, rfl⟩ := hvertex g
      change forward (back (P.base (D.vertex e))) = P.base (D.vertex e)
      rw [show back (P.base (D.vertex e)) = v (D.vertex e) from P.lift_base _ _ _ _,
        hv, hforward, D.map_base]
    · intro i
      change forward (back (P.stable i)) = P.stable i
      rw [show back (P.stable i) = q (T.stable i) from P.lift_stable _ _ _ i,
        hforward, D.map_stable]
  constructor
  · apply le_antisymm _ D.kernelImage_le_ker
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    have h := DFunLike.congr_fun hback_map x
    change back (D.map x) = q x at h
    rw [show D.map x = 1 from hx, map_one] at h
    exact h.symm
  · intro k
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective D.kernelImage (back k)
    refine ⟨x, ?_⟩
    have h := congrArg forward hx
    rw [hforward] at h
    exact h.trans (DFunLike.congr_fun hforward_back k)

include hc hkernel hvertex hedge in
/-- The resulting quotient is again a central extension. -/
theorem map_central : Central D.map := by
  rw [Central, (D.map_ker_and_surjective hc hkernel hvertex hedge).1]
  exact D.kernelImage_central hc hkernel

end HNNFamilyQuotient
end SmallPresentationStatements.Homology
