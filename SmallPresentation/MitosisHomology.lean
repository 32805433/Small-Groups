module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The explicit algebra in the finite-mitosis homology calculation

The degree-one edge map is an isomorphism. The degree-two edge map has cokernel equal to
the reduced diagonal's target, with the first-coordinate map identified as minus the diagonal.
The final theorems consume exactness hypotheses from Mayer–Vietoris; they do not assume the
paper-specific homology calculation as an external input.
-/
@[expose] public section

namespace SmallPresentationStatements.MitosisHomology

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The degree-one edge map `(b,c) ↦ (c,-b-c)` and its explicit inverse. -/
def edge₁ (A : Type*) [AddCommGroup A] : A × A ≃+ A × A where
  toFun v := (v.2, -v.1 - v.2)
  invFun v := (-v.1 - v.2, v.1)
  left_inv v := by ext <;> simp; abel
  right_inv v := by ext <;> simp
  map_add' u v := by ext <;> simp; abel

/-- The degree-two edge map in the Künneth coordinates of the manuscript. -/
def edge₂ (δ : B →+ C) : B × B →+ B × B × C where
  toFun v := (v.2, -v.1 - v.2, -δ v.1)
  map_zero' := by simp
  map_add' u v := by ext <;> simp [map_add] <;> abel

/-- The quotient coordinate `ψ(u,v,w) = w - δ(u+v)`. -/
def quotientCoordinate (δ : B →+ C) : B × B × C →+ C where
  toFun v := v.2.2 - δ (v.1 + v.2.1)
  map_zero' := by simp
  map_add' u v := by simp [map_add]; abel

@[simp] theorem quotientCoordinate_edge₂ (δ : B →+ C) (v : B × B) :
    quotientCoordinate δ (edge₂ δ v) = 0 := by
  simp [quotientCoordinate, edge₂, map_add, map_neg, map_sub]

@[simp] theorem quotientCoordinate_section (δ : B →+ C) (c : C) :
    quotientCoordinate δ (0, 0, c) = c := by
  simp [quotientCoordinate]

theorem quotientCoordinate_surjective (δ : B →+ C) :
    Function.Surjective (quotientCoordinate δ) :=
  fun c ↦ ⟨(0, 0, c), quotientCoordinate_section δ c⟩

theorem range_edge₂_eq_ker (δ : B →+ C) :
    (edge₂ δ).range = (quotientCoordinate δ).ker := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact quotientCoordinate_edge₂ δ u
  · intro hv
    have hw : v.2.2 = δ (v.1 + v.2.1) := sub_eq_zero.mp hv
    refine ⟨(-v.1 - v.2.1, v.1), ?_⟩
    ext
    · rfl
    · simp [edge₂]
    · change -δ (-v.1 - v.2.1) = v.2.2
      rw [hw]
      simp [map_sub, map_add, add_comm]

/-- The exact integral cokernel, with an explicit section and no rank argument. -/
def cokernelEquiv (δ : B →+ C) : (B × B × C) ⧸ (edge₂ δ).range ≃+ C :=
  (QuotientAddGroup.quotientAddEquivOfEq (range_edge₂_eq_ker δ)).trans
    (QuotientAddGroup.quotientKerEquivOfRightInverse (quotientCoordinate δ)
      (fun c ↦ (0, 0, c)) (quotientCoordinate_section δ))

@[simp] theorem cokernelEquiv_mk (δ : B →+ C) (v : B × B × C) :
    cokernelEquiv δ (QuotientAddGroup.mk v) = v.2.2 - δ (v.1 + v.2.1) := by
  rw [cokernelEquiv, AddEquiv.trans_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

/-- The induced first-coordinate inclusion is minus the reduced diagonal. -/
@[simp] theorem cokernelEquiv_first (δ : B →+ C) (b : B) :
    cokernelEquiv δ (QuotientAddGroup.mk (b, 0, 0)) = -δ b := by simp

section FirstHomology

variable {H D E : Type*} [AddCommGroup H] [AddCommGroup D] [AddCommGroup E]

/-- The entire vertex `H₁` vanishes because the preceding edge map is onto. -/
theorem vertexMap_eq_zero (v : A × A →+ H)
    (h : v.comp (edge₁ A).toAddMonoidHom = 0) : v = 0 := by
  ext a
  obtain ⟨b, rfl⟩ := (edge₁ A).surjective a
  exact DFunLike.congr_fun h b

/-- The degree-one Mayer–Vietoris conclusion, given exactness at the two middle terms.
For finite mitosis, `D = ℤ × ℤ` and the following degree-zero edge map is zero. -/
noncomputable def firstHomologyEquiv (v : A × A →+ H) (c : H →+ D)
    (hleft : v.comp (edge₁ A).toAddMonoidHom = 0)
    (hmid : c.ker = v.range) (hright : c.range = (0 : D →+ E).ker) : H ≃+ D := by
  have hv := vertexMap_eq_zero v hleft
  have hc : Function.Injective c := by
    apply (AddMonoidHom.ker_eq_bot_iff c).mp
    simpa [hv] using hmid
  have hs : Function.Surjective c := by
    apply (AddMonoidHom.range_eq_top).mp
    simpa using hright
  exact AddEquiv.ofBijective c ⟨hc, hs⟩

end FirstHomology

section SecondHomology

variable {H : Type*} [AddCommGroup H]

/-- Injectivity of the next edge map makes the connecting homomorphism zero. -/
theorem connectingMap_eq_zero (d : H →+ A × A)
    (h : (edge₁ A).toAddMonoidHom.comp d = 0) : d = 0 := by
  apply AddMonoidHom.ext
  intro x
  apply (edge₁ A).injective
  simpa using DFunLike.congr_fun h x

theorem vertex₂_surjective (q : B × B × C →+ H) (d : H →+ A × A)
    (hmid : q.range = d.ker) (hright : (edge₁ A).toAddMonoidHom.comp d = 0) :
    Function.Surjective q := by
  have hd := connectingMap_eq_zero d hright
  apply (AddMonoidHom.range_eq_top).mp
  simpa [hd] using hmid

/-- The degree-two Mayer–Vietoris calculation with explicit edge maps. -/
noncomputable def secondHomologyEquiv (δ : B →+ C)
    (q : B × B × C →+ H) (d : H →+ A × A)
    (hleft : q.ker = (edge₂ δ).range) (hmid : q.range = d.ker)
    (hright : (edge₁ A).toAddMonoidHom.comp d = 0) : H ≃+ C :=
  (QuotientAddGroup.quotientKerEquivOfSurjective q
    (vertex₂_surjective q d hmid hright)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hleft).trans (cokernelEquiv δ))

theorem secondHomologyEquiv_vertex (δ : B →+ C)
    (q : B × B × C →+ H) (d : H →+ A × A)
    (hleft : q.ker = (edge₂ δ).range) (hmid : q.range = d.ker)
    (hright : (edge₁ A).toAddMonoidHom.comp d = 0) (v : B × B × C) :
    secondHomologyEquiv δ q d hleft hmid hright (q v) =
      v.2.2 - δ (v.1 + v.2.1) := by
  have hmk :
      (QuotientAddGroup.quotientKerEquivOfSurjective q
        (vertex₂_surjective q d hmid hright)).symm (q v) = QuotientAddGroup.mk v := by
    apply (QuotientAddGroup.quotientKerEquivOfSurjective q
      (vertex₂_surjective q d hmid hright)).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [secondHomologyEquiv, AddEquiv.trans_apply, hmk, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk, cokernelEquiv_mk]

theorem secondHomologyEquiv_first (δ : B →+ C)
    (q : B × B × C →+ H) (d : H →+ A × A)
    (hleft : q.ker = (edge₂ δ).range) (hmid : q.range = d.ker)
    (hright : (edge₁ A).toAddMonoidHom.comp d = 0) (b : B) :
    secondHomologyEquiv δ q d hleft hmid hright (q (b, 0, 0)) = -δ b := by
  simp [secondHomologyEquiv_vertex]

end SecondHomology

/-- Naturality of the reduced diagonal and the zero map on `H₁` kill the composite on `H₂`.
Here `T` is the map induced on the tensor-product summands by the zero `H₁` map. -/
theorem two_mitoses_zero {D : Type*} [AddCommGroup D]
    (δ : B →+ C) (δ' : C →+ D) (i : B →+ C) (i' : C →+ D) (T : C →+ D)
    (hnat : δ'.comp i = T.comp δ) (hT : T = 0) (hi' : i' = -δ') : i'.comp i = 0 := by
  ext b
  have h := DFunLike.congr_fun hnat b
  simp only [AddMonoidHom.comp_apply, hT, AddMonoidHom.zero_apply] at h
  simp [hi', h]

theorem tensorSquare_zero {A' : Type*} [AddCommGroup A'] (f : A →+ A') (hf : f = 0) :
    TensorProduct.map f.toIntLinearMap f.toIntLinearMap = 0 := by
  have hlin : f.toIntLinearMap = 0 := by ext a; simp [hf]
  simp [hlin]

/-- The actual tensor-square specialization of reduced-diagonal naturality. -/
theorem two_mitoses_zero_of_tensor_naturality {A' : Type*} [AddCommGroup A']
    (δ : B →+ TensorProduct ℤ A A)
    (δ' : TensorProduct ℤ A A →+ TensorProduct ℤ A' A')
    (i : B →+ TensorProduct ℤ A A)
    (i' : TensorProduct ℤ A A →+ TensorProduct ℤ A' A')
    (f : A →+ A') (hf : f = 0)
    (hnat : δ'.comp i =
      (TensorProduct.map f.toIntLinearMap f.toIntLinearMap).toAddMonoidHom.comp δ)
    (hi' : i' = -δ') : i'.comp i = 0 := by
  apply two_mitoses_zero δ δ' i i' _ hnat _ hi'
  rw [tensorSquare_zero f hf]
  rfl

end SmallPresentationStatements.MitosisHomology
