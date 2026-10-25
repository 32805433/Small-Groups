module

public import SmallPresentation.PackingBase

/-! The signed quotient of the partition product is exactly the product of
the signed quotients in individual fibers. All maps respect the literal code rows. -/
@[expose] public section

namespace SmallPresentationStatements.PackingBaseProduct

open Word

variable {L : ℕ} (Q : FP 2 L) {V C : Type} (π : V → C)

abbrev Fiber (c : C) := {v : V // π v = c}

def fiberRow {c : C} (v w : Fiber π c) (i : Fin L) : FreeGroup (Fiber π c) :=
  eval ![eval ![FreeGroup.of v, FreeGroup.of w] code₁,
    eval ![FreeGroup.of v, FreeGroup.of w] code₂] (Q.relator i)

def fiberRelators (c : C) : Set (FreeGroup (Fiber π c)) :=
  {z | ∃ v w : Fiber π c, v ≠ w ∧ ∃ i, z = fiberRow Q π v w i}

abbrev FiberGroup (c : C) := PresentedGroup (fiberRelators Q π c)
abbrev Product := ∀ c : C, FiberGroup Q π c

theorem factor_row {c : C} (v w : Fiber π c) (i : Fin L) :
    HostPartition.factor π c (fiberRow Q π v w i) = PackingBase.row Q π v.1 w.1 i := by
  simp only [fiberRow, PackingBase.row, PackingBase.map_pair_eval, HostPartition.factor,
    FreeGroup.lift_apply_of]

noncomputable def fiberToBase (c : C) : FiberGroup Q π c →* PackingBase.Group Q π :=
  PresentedGroup.toGroup (f := fun v ↦ PackingBase.lamp Q π v.1) (by
    rintro _ ⟨v, w, hvw, i, rfl⟩
    simp only [fiberRow, PackingBase.map_pair_eval, FreeGroup.lift_apply_of]
    have h := PackingBase.quotient_row Q π v.1 w.1 (v.property.trans w.property.symm)
      (fun h ↦ hvw (Subtype.ext h)) i
    simpa only [PackingBase.row, PackingBase.map_pair_eval, PackingBase.lamp] using h)

@[simp] theorem fiberToBase_of (c : C) (v : Fiber π c) :
    fiberToBase Q π c (PresentedGroup.of v) = PackingBase.lamp Q π v.1 :=
  PresentedGroup.toGroup.of _

theorem fibers_commute : Pairwise fun c d ↦ ∀ a b,
    Commute (fiberToBase Q π c a) (fiberToBase Q π d b) := by
  intro c d h a b
  obtain ⟨a, rfl⟩ := PresentedGroup.mk_surjective (fiberRelators Q π c) a
  obtain ⟨b, rfl⟩ := PresentedGroup.mk_surjective (fiberRelators Q π d) b
  apply HostPartition.free_lifts_commute
    ((fiberToBase Q π c).comp (PresentedGroup.mk _))
    ((fiberToBase Q π d).comp (PresentedGroup.mk _))
  intro v w
  change Commute (fiberToBase Q π c (PresentedGroup.of v))
    (fiberToBase Q π d (PresentedGroup.of w))
  rw [fiberToBase_of, fiberToBase_of]
  apply Commute.map
  apply HostPartition.generators_commute
  simpa only [v.property, w.property] using h

section Finite
variable [Fintype C] [DecidableEq C]

noncomputable def fromProduct : Product Q π →* PackingBase.Group Q π :=
  MonoidHom.noncommPiCoprod (fiberToBase Q π) (fibers_commute Q π)

def quotientFactors : HostPartition.Product π →* Product Q π :=
  MonoidHom.pi (fun c ↦ (PresentedGroup.mk (fiberRelators Q π c)).comp
    (Pi.evalMonoidHom (fun c ↦ FreeGroup (Fiber π c)) c))

omit [Fintype C] in
theorem quotientFactors_single (c : C) (x : FreeGroup (Fiber π c)) :
    quotientFactors Q π (Pi.mulSingle c x) =
      Pi.mulSingle c (PresentedGroup.mk (fiberRelators Q π c) x) := by
  funext d
  by_cases h : c = d
  · subst d
    simp [quotientFactors]
  · simp [quotientFactors, h]

def toProductPre : HostPartition.Group π →* Product Q π :=
  (quotientFactors Q π).comp (HostPartition.toProduct π)

omit [Fintype C] in
@[simp] theorem toProductPre_generator (v : V) :
    toProductPre Q π (HostPartition.generator π v) =
      Pi.mulSingle (π v) (PresentedGroup.of (rels := fiberRelators Q π (π v)) ⟨v, rfl⟩) := by
  simp only [toProductPre, MonoidHom.comp_apply, HostPartition.toProduct_generator,
    HostPartition.productGenerator, quotientFactors_single, PresentedGroup.of]

omit [Fintype C] in
theorem toProductPre_factor (c : C) (x : FreeGroup (Fiber π c)) :
    toProductPre Q π (HostPartition.factor π c x) =
      Pi.mulSingle c (PresentedGroup.mk (fiberRelators Q π c) x) := by
  have h : (toProductPre Q π).comp (HostPartition.factor π c) =
      (MonoidHom.mulSingle (fun c ↦ FiberGroup Q π c) c).comp (PresentedGroup.mk _) := by
    apply FreeGroup.ext_hom
    intro v
    simp only [MonoidHom.comp_apply, HostPartition.factor, FreeGroup.lift_apply_of,
      toProductPre_generator, MonoidHom.mulSingle_apply]
    rcases v with ⟨v, hv⟩
    subst c
    rfl
  exact DFunLike.congr_fun h x

omit [Fintype C] in
theorem toProductPre_row (v w : V) (hπ : π v = π w) (hvw : v ≠ w) (i : Fin L) :
    toProductPre Q π (PackingBase.row Q π v w i) = 1 := by
  let v' : Fiber π (π v) := ⟨v, rfl⟩
  let w' : Fiber π (π v) := ⟨w, hπ.symm⟩
  rw [← factor_row Q π v' w' i, toProductPre_factor]
  have hrow : fiberRow Q π v' w' i ∈ fiberRelators Q π (π v) :=
    ⟨v', w', fun h ↦ hvw (congrArg Subtype.val h), i, rfl⟩
  rw [PresentedGroup.one_of_mem hrow]
  simp

def toProduct : PackingBase.Group Q π →* Product Q π :=
  QuotientGroup.lift (PackingBase.kernel Q π) (toProductPre Q π) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨v, w, hπ, hvw, i, rfl⟩
    exact toProductPre_row Q π v w hπ hvw i)

omit [Fintype C] in
@[simp] theorem toProduct_quotient (x : HostPartition.Group π) :
    toProduct Q π (PackingBase.quotient Q π x) = toProductPre Q π x := rfl

omit [Fintype C] in
@[simp] theorem toProduct_lamp (v : V) :
    toProduct Q π (PackingBase.lamp Q π v) =
      Pi.mulSingle (π v) (PresentedGroup.of (rels := fiberRelators Q π (π v)) ⟨v, rfl⟩) :=
  toProductPre_generator Q π v

theorem from_to : (fromProduct Q π).comp (toProduct Q π) = MonoidHom.id _ := by
  apply PackingBase.hom_ext Q π
  intro v
  simp [fromProduct]

theorem to_from : (toProduct Q π).comp (fromProduct Q π) = MonoidHom.id _ := by
  apply MonoidHom.pi_ext
  intro c
  have h : (toProduct Q π).comp (fiberToBase Q π c) =
      MonoidHom.mulSingle (fun c ↦ FiberGroup Q π c) c := by
    apply PresentedGroup.ext
    intro v
    simp only [MonoidHom.comp_apply, fiberToBase_of, toProduct_lamp, MonoidHom.mulSingle_apply]
    rcases v with ⟨v, hv⟩
    subst c
    rfl
  intro x
  simpa only [MonoidHom.comp_apply, fromProduct, MonoidHom.noncommPiCoprod_mulSingle,
    MonoidHom.id_apply, MonoidHom.mulSingle_apply] using DFunLike.congr_fun h x

noncomputable def productEquiv : PackingBase.Group Q π ≃* Product Q π where
  toFun := toProduct Q π
  invFun := fromProduct Q π
  left_inv x := DFunLike.congr_fun (from_to Q π) x
  right_inv x := DFunLike.congr_fun (to_from Q π) x
  map_mul' := (toProduct Q π).map_mul

omit [Fintype C] in
theorem fiberToBase_injective (c : C) : Function.Injective (fiberToBase Q π c) := by
  intro a b hab
  have h : (toProduct Q π).comp (fiberToBase Q π c) =
      MonoidHom.mulSingle (fun c ↦ FiberGroup Q π c) c := by
    apply PresentedGroup.ext
    intro v
    simp only [MonoidHom.comp_apply, fiberToBase_of, toProduct_lamp, MonoidHom.mulSingle_apply]
    rcases v with ⟨v, hv⟩
    subst c
    rfl
  have hh := congrArg (toProduct Q π) hab
  have ha := DFunLike.congr_fun h a
  have hb := DFunLike.congr_fun h b
  simp only [MonoidHom.comp_apply] at ha hb
  rw [ha, hb] at hh
  simpa using congrFun hh c

end Finite

theorem signedRow_eval {H : Type*} [Group H] {d : ℕ} (f : Fin d → H)
    (v w : Fin d) (i : Fin L) :
    eval f (SignedCoding.row Q v w i) =
      eval ![eval ![f v, f w] code₁, eval ![f v, f w] code₂] (Q.relator i) := by
  simp only [SignedCoding.row, eval_subst, SignedCoding.eval_codeWord]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem fiber_row_eq_one {c : C} (v w : Fiber π c) (hvw : v ≠ w) (i : Fin L) :
    eval ![eval ![PresentedGroup.of (rels := fiberRelators Q π c) v, PresentedGroup.of w] code₁,
      eval ![PresentedGroup.of v, PresentedGroup.of w] code₂] (Q.relator i) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := fiberRelators Q π c) ⟨v, w, hvw, i, rfl⟩
  simpa only [fiberRow, PackingBase.map_pair_eval, PresentedGroup.of] using h

variable {d : ℕ} (c : C) (e : Fiber π c ≃ Fin d)

noncomputable def fiberToCode : FiberGroup Q π c →* SignedCoding.CodedGroup Q d :=
  PresentedGroup.toGroup (f := fun v ↦ PresentedGroup.of (e v)) (by
    rintro _ ⟨v, w, hvw, i, rfl⟩
    simp only [fiberRow, PackingBase.map_pair_eval, FreeGroup.lift_apply_of]
    rw [← signedRow_eval]
    exact SignedCoding.row_eq_one Q (e v) (e w) (fun h ↦ hvw (e.injective h)) i)

noncomputable def codeToFiber : SignedCoding.CodedGroup Q d →* FiberGroup Q π c :=
  PresentedGroup.toGroup (f := fun v ↦ PresentedGroup.of (e.symm v)) (by
    rintro _ ⟨v, w, hvw, i, rfl⟩
    change eval (fun v ↦ PresentedGroup.of (e.symm v)) (SignedCoding.row Q v w i) = 1
    rw [signedRow_eval]
    exact fiber_row_eq_one Q π (e.symm v) (e.symm w) (fun h ↦ hvw (e.symm.injective h)) i)

@[simp] theorem fiberToCode_of (v : Fiber π c) :
    fiberToCode Q π c e (PresentedGroup.of v) = PresentedGroup.of (e v) :=
  PresentedGroup.toGroup.of _

@[simp] theorem codeToFiber_of (v : Fin d) :
    codeToFiber Q π c e (PresentedGroup.of v) = PresentedGroup.of (e.symm v) :=
  PresentedGroup.toGroup.of _

noncomputable def fiberCodeEquiv : FiberGroup Q π c ≃* SignedCoding.CodedGroup Q d where
  toFun := fiberToCode Q π c e
  invFun := codeToFiber Q π c e
  left_inv x := by
    have h : (codeToFiber Q π c e).comp (fiberToCode Q π c e) = MonoidHom.id _ := by
      apply PresentedGroup.ext
      intro v
      simp
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (fiberToCode Q π c e).comp (codeToFiber Q π c e) = MonoidHom.id _ := by
      apply PresentedGroup.ext
      intro v
      simp
    exact DFunLike.congr_fun h x
  map_mul' := (fiberToCode Q π c e).map_mul

noncomputable def sourceHom (v w : Fin d) (hvw : v ≠ w) : Q.Group →* PackingBase.Group Q π :=
  (fiberToBase Q π c).comp ((codeToFiber Q π c e).comp (SignedCoding.sourceHom Q v w hvw))

theorem sourceHom_of (v w : Fin d) (hvw : v ≠ w) (j : Fin 2) :
    sourceHom Q π c e v w hvw (PresentedGroup.of j) =
      eval ![PackingBase.lamp Q π (e.symm v).1, PackingBase.lamp Q π (e.symm w).1]
        (![code₁, code₂] j) := by
  simp only [sourceHom, MonoidHom.comp_apply, SignedCoding.sourceHom, PresentedGroup.toGroup.of,
    map_eval, SignedCoding.eval_codeWord]
  congr 1
  funext k
  fin_cases k <;> simp

theorem sourceHom_injective [DecidableEq C] (v w : Fin d) (hvw : v ≠ w)
    (hsource : Function.Injective (SignedCoding.sourceHom Q v w hvw)) :
    Function.Injective (sourceHom Q π c e v w hvw) :=
  (fiberToBase_injective Q π c).comp ((fiberCodeEquiv Q π c e).symm.injective.comp hsource)

end SmallPresentationStatements.PackingBaseProduct
