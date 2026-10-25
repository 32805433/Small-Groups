module

public import SmallPresentation.FourCentralAction
public import SmallPresentation.FourHostMap

/-! The literal packed word in the centralized host and its final quotient. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral
open Word

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

def basePacked : Host.Kernel p :=
  (List.ofFn fun i : Fin L ↦ PackingBase.row Q (Host.residue p)
    (i.val : ZMod (p ^ 2)) ((p + i.val : ℕ) : ZMod (p ^ 2)) i).prod

def packed : C Q p := mk Q p (basePacked Q p)

variable (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

noncomputable abbrev PackedModel :=
  Model Q p u hu ⧸ SemidirectOrbit.totalKernel (action Q p u hu) (packed Q p)

noncomputable def packProjection : Model Q p u hu →* PackedModel Q p u hu := QuotientGroup.mk' _
noncomputable def fromHost : Host.Model p u hu →* PackedModel Q p u hu :=
  (packProjection Q p u hu).comp (projection Q p u hu)

noncomputable def hostGenerators : Fin 2 → Host.Model p u hu :=
  ![Host.a p u hu * Host.t p u hu, Host.s p u hu]

@[simp] theorem hostGenerators_s : eval (hostGenerators p u hu) (gen 1) = Host.s p u hu := rfl
@[simp] theorem hostGenerators_A : eval (hostGenerators p u hu) eliminatedA = Host.a p u hu := by
  simp only [eliminatedA, eval_append, eval_gen, eval_inverse, eliminatedT, eval_commutator,
    hostGenerators, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact Elimination.recover_a _ _ _ (Host.a_s p u hu) (Host.t_s p u hu)
@[simp] theorem hostGenerators_T : eval (hostGenerators p u hu) eliminatedT = Host.t p u hu := by
  simp only [eliminatedT, eval_commutator, eval_gen,
    hostGenerators, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact Elimination.recover_t _ _ _ (Host.a_s p u hu) (Host.t_s p u hu)

theorem packed_in_host : eval (hostGenerators p u hu)
    (packedWord Q p eliminatedA eliminatedT) = SemidirectProduct.inl (basePacked Q p) := by
  rw [FourPacking.packed_eval, hostGenerators_A, hostGenerators_T]
  have hlamp (n : ℕ) : HostAlgebra.lamp (Host.a p u hu) (Host.t p u hu) n =
      SemidirectProduct.inl (Host.lamp p n) := Host.a_tpow p u hu n
  simp_rw [hlamp]
  rw [basePacked, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_def, PackingBase.row, SlotIsolation.encodedValue,
    PackingBase.map_pair_eval, eval_subst_pair]
  rfl

theorem fromHost_kills_packed : fromHost Q p u hu (SemidirectProduct.inl (basePacked Q p)) = 1 := by
  change packProjection Q p u hu (projection Q p u hu _) = 1
  rw [projection_inl]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure (Set.mem_singleton _)

noncomputable def generators : Fin 2 → PackedModel Q p u hu :=
  fun j ↦ fromHost Q p u hu (hostGenerators p u hu j)

@[simp] theorem eval_generators (w : Word 2) :
    eval (generators Q p u hu) w = fromHost Q p u hu (eval (hostGenerators p u hu) w) :=
  (map_eval (fromHost Q p u hu) (hostGenerators p u hu) w).symm

theorem generators_relator [Fact (1 < p)] (i : Fin 4) :
    eval (generators Q p u hu) ((fourPresentation Q p).relator i) = 1 := by
  rw [eval_generators]
  fin_cases i
  · change fromHost Q p u hu (eval _ actionRow) = 1
    simp only [actionRow, eval_append, eval_conjugate, eval_power, eval_inverse,
      hostGenerators_s, hostGenerators_T, Host.t_s, mul_inv_cancel, map_one]
  · change fromHost Q p u hu (eval _
      (conjugate eliminatedA (power eliminatedT (p ^ 2)) ++ inverse eliminatedA)) = 1
    simp only [eval_append, eval_conjugate, eval_power, eval_inverse,
      hostGenerators_A, hostGenerators_T, Host.a_periodic, mul_inv_cancel, map_one]
  · change fromHost Q p u hu (eval _ commutationRow) = 1
    have h := (PackingAlgebra.commutator_eq_one_iff _ _).mpr (Host.a_commutes_t p u hu)
    simp only [commutationRow, eval_commutator, eval_conjugate,
      hostGenerators_A, hostGenerators_T]
    change fromHost Q p u hu (Elimination.commutator _ _) = 1
    rw [h, map_one]
  · change fromHost Q p u hu (eval (hostGenerators p u hu)
      (packedWord Q p eliminatedA eliminatedT)) = 1
    rw [packed_in_host, fromHost_kills_packed]

noncomputable def toPacked [Fact (1 < p)] :
    (fourPresentation Q p).Group →* PackedModel Q p u hu :=
  PresentedGroup.toGroup (f := generators Q p u hu) (by
    rintro _ ⟨i,rfl⟩
    exact generators_relator Q p u hu i)

@[simp] theorem toPacked_of [Fact (1 < p)] (j : Fin 2) :
    toPacked Q p u hu (PresentedGroup.of j) = generators Q p u hu j := PresentedGroup.toGroup.of _

end SmallPresentationStatements.FourCentral
