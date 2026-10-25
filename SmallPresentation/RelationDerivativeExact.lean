module

public import SmallPresentation.RelationDerivative

/-! A normalized set-theoretic section contracts the Cayley chain complex. This
proves the relation-module embedding and the presentation exact sequence without
any geometric or small-cancellation hypotheses. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

variable {X H : Type} [Group H] (p : FreeGroup X →* H)

/-- A normalized choice of a free word representing every element. -/
structure Section where
  word : H → FreeGroup X
  evaluates : ∀ h, p (word h) = h
  at_one : word 1 = 1

open Classical in
noncomputable def sectionOfSurjective (hp : Function.Surjective p) : Section p where
  word h := if h = 1 then 1 else Classical.choose (hp h)
  evaluates h := by split_ifs with h1; simp [h1]; exact Classical.choose_spec (hp h)
  at_one := by simp

variable (s : Section p)

/-- Close a word path using the chosen words at its endpoints. -/
def sectionLoop (h : H) (w : FreeGroup X) : p.ker :=
  ⟨s.word h * w * (s.word (h * p w))⁻¹, by
    change p (s.word h * w * (s.word (h * p w))⁻¹) = 1
    simp [s.evaluates]⟩

@[simp] theorem sectionLoop_one (h : H) : sectionLoop p s h 1 = 1 := by
  apply Subtype.ext
  simp [sectionLoop]

theorem sectionLoop_mul (h : H) (u v : FreeGroup X) :
    sectionLoop p s h (u * v) =
      sectionLoop p s h u * sectionLoop p s (h * p u) v := by
  apply Subtype.ext
  simp [sectionLoop, mul_assoc]

theorem sectionLoop_inv (h : H) (w : FreeGroup X) :
    sectionLoop p s h w⁻¹ = (sectionLoop p s (h * (p w)⁻¹) w)⁻¹ := by
  apply Subtype.ext
  simp [sectionLoop, mul_assoc]

/-- Send each labelled edge to its closed loop in the abelianized kernel. -/
def retractChains : Chains H X →+ Additive (Abelianization p.ker) :=
  FreeAbelianGroup.lift (fun e ↦
    Additive.ofMul (Abelianization.of (sectionLoop p s e.1 (FreeGroup.of e.2))))

@[simp] theorem retractChains_of (h : H) (x : X) :
    retractChains p s (FreeAbelianGroup.of (h, x)) =
      Additive.ofMul (Abelianization.of (sectionLoop p s h (FreeGroup.of x))) := by
  simp [retractChains]

/-- Telescoping the edge loops gives the loop around the whole path. -/
theorem retract_shift_derivative (w : FreeGroup X) (h : H) :
    retractChains p s (shift h (derivative p w)) =
      Additive.ofMul (Abelianization.of (sectionLoop p s h w)) := by
  induction w using FreeGroup.induction_on generalizing h with
  | one => simp
  | of x => simp
  | inv_of x ih =>
    rw [derivative_inv, map_neg, map_neg, ← shift_mul, ih, sectionLoop_inv]
    rfl
  | mul u v hu hv =>
    rw [derivative_mul, map_add, map_add, ← shift_mul, hu, hv, sectionLoop_mul, map_mul]
    rfl

@[simp] theorem sectionLoop_kernel (w : p.ker) : sectionLoop p s 1 w.val = w := by
  apply Subtype.ext
  simp [sectionLoop, show p w.val = 1 from w.property, s.at_one]

/-- The relation derivative has a left inverse as a map of abelian groups. -/
theorem retract_relationDerivative (c : Additive (Abelianization p.ker)) :
    retractChains p s (relationDerivative p c) = c := by
  induction c using QuotientGroup.induction_on with
  | H w =>
    change retractChains p s (derivative p w.val) = _
    rw [← shift_one (derivative p w.val), retract_shift_derivative, sectionLoop_kernel]
    rfl

theorem relationDerivative_injective (hp : Function.Surjective p) :
    Function.Injective (relationDerivative p) :=
  Function.LeftInverse.injective (retract_relationDerivative p (sectionOfSurjective p hp))

/-- Edge chains of the chosen paths to vertices. -/
def sectionChains : Vertices H →+ Chains H X :=
  FreeAbelianGroup.lift (fun h ↦ derivative p (s.word h))

@[simp] theorem sectionChains_of (h : H) :
    sectionChains p s (FreeAbelianGroup.of h) = derivative p (s.word h) := by
  simp [sectionChains]

theorem derivative_sectionLoop (h : H) (w : FreeGroup X) :
    derivative p (sectionLoop p s h w).val =
      derivative p (s.word h) + shift h (derivative p w) -
        derivative p (s.word (h * p w)) := by
  change derivative p (s.word h * w * (s.word (h * p w))⁻¹) = _
  rw [derivative_mul, derivative_mul, derivative_inv]
  simp only [map_mul, s.evaluates, map_neg, ← shift_mul, mul_inv_cancel, shift_one]
  simp [sub_eq_add_neg]

/-- A chain differs from its closed-loop chain by the chosen path to its boundary. -/
theorem relationDerivative_retract (c : Chains H X) :
    relationDerivative p (retractChains p s c) = c - sectionChains p s (boundary p c) := by
  have he : (relationDerivative p).comp (retractChains p s) =
      AddMonoidHom.id _ - (sectionChains p s).comp (boundary p) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨h, x⟩
    simp only [AddMonoidHom.comp_apply, retractChains_of, relationDerivative_of]
    rw [derivative_sectionLoop]
    simp only [derivative_of, shift_of, mul_one, AddMonoidHom.sub_apply,
      AddMonoidHom.id_apply, AddMonoidHom.comp_apply, boundary_of, map_sub, sectionChains_of]
    abel
  exact DFunLike.congr_fun he c

/-- Exactness at the group of labelled edge chains. -/
theorem boundary_ker_eq_relationDerivative_range (hp : Function.Surjective p) :
    (boundary p).ker = (relationDerivative p).range := by
  apply le_antisymm
  · intro c hc
    refine ⟨retractChains p (sectionOfSurjective p hp) c, ?_⟩
    rw [relationDerivative_retract, show boundary p c = 0 from hc, map_zero, sub_zero]
  · rintro _ ⟨c, rfl⟩
    exact boundary_relationDerivative p c

/-- Sum of the coefficients of a vertex chain. -/
def augmentation : Vertices H →+ ℤ := FreeAbelianGroup.lift (fun _ ↦ 1)

omit [Group H] in
@[simp] theorem augmentation_of (h : H) :
    augmentation (FreeAbelianGroup.of h) = 1 := rfl

@[simp] theorem augmentation_boundary (c : Chains H X) :
    augmentation (boundary p c) = 0 := by
  have he : augmentation.comp (boundary p) = 0 := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨h, x⟩
    simp
  exact DFunLike.congr_fun he c

theorem boundary_sectionChains (c : Vertices H) :
    boundary p (sectionChains p s c) = c - augmentation c • FreeAbelianGroup.of (1 : H) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of h => simp [boundary_derivative, s.evaluates]
  | neg c ih => simp only [map_neg, ih, neg_zsmul]; abel
  | add c d hc hd => simp only [map_add, hc, hd, add_zsmul]; abel

/-- Exactness at the group of vertex chains. -/
theorem augmentation_ker_eq_boundary_range (hp : Function.Surjective p) :
    (augmentation (H := H)).ker = (boundary p).range := by
  apply le_antisymm
  · intro c hc
    refine ⟨sectionChains p (sectionOfSurjective p hp) c, ?_⟩
    rw [boundary_sectionChains, show augmentation c = 0 from hc, zero_smul, sub_zero]
  · rintro _ ⟨c, rfl⟩
    exact augmentation_boundary p c

theorem augmentation_surjective : Function.Surjective (augmentation (H := H)) := by
  intro n
  refine ⟨n • FreeAbelianGroup.of (1 : H), ?_⟩
  simp

/-- The complete presentation exact sequence, with the specified derivative and boundary. -/
theorem presentation_exact (hp : Function.Surjective p) :
    Function.Injective (relationDerivative p) ∧
      (boundary p).ker = (relationDerivative p).range ∧
      (augmentation (H := H)).ker = (boundary p).range ∧
      Function.Surjective (augmentation (H := H)) :=
  ⟨relationDerivative_injective p hp, boundary_ker_eq_relationDerivative_range p hp,
    augmentation_ker_eq_boundary_range p hp, augmentation_surjective⟩

end SmallPresentationStatements.RelationDerivative
