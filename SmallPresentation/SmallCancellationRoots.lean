module

public import SmallPresentation.FreeGroupCentralizerWords
public import SmallPresentation.RelationDerivativeRows

/-! Metric cyclic-origin uniqueness makes the literal free lifts of relator rows
root-free. Consequently the generic free-group centralizer bookkeeping applies
to the actual lifted presentation used by the homology and identity proofs. -/
@[expose] public section

namespace SmallPresentationStatements.FreeGroupCentralizer

open FreeGroup

variable {X : Type*}

/-- Every word consisting of positive free generators is reduced. -/
theorem positiveWord_isReduced (v : List X) : IsReduced (v.map (fun x ↦ (x, true))) := by
  induction v with
  | nil => simp
  | cons a v ih =>
    cases v with
    | nil => simp
    | cons b v => simpa [isReduced_cons_cons] using ih

/-- Positive free-generator words are cyclically reduced, including at the cyclic seam. -/
theorem positiveWord_isCyclicallyReduced (v : List X) :
    IsCyclicallyReduced (v.map (fun x ↦ (x, true))) := by
  refine ⟨positiveWord_isReduced v, ?_⟩
  intro a ha b hb _
  simp only [List.getLast?_map, Option.mem_map] at ha
  simp only [List.head?_map, Option.mem_map] at hb
  obtain ⟨a, _, rfl⟩ := ha
  obtain ⟨b, _, rfl⟩ := hb
  rfl

/-- The literal signed word of a positive product has the expected free-group value. -/
theorem mk_positiveWord (v : List X) :
    FreeGroup.mk (v.map (fun x ↦ (x, true))) = (v.map FreeGroup.of).prod := by
  have h := FreeGroup.lift_mk (f := FreeGroup.of) (L := v.map (fun x ↦ (x, true)))
  simpa only [FreeGroup.lift_of_apply, List.map_map, Function.comp_def, Bool.cond_true] using h

end SmallPresentationStatements.FreeGroupCentralizer

namespace SmallPresentationStatements.RelativeSmallCancellation

open RelationDerivative.CanonicalSchur FreeGroupCentralizer

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]
variable (rows : ∀ i, Fin (length i) → Syllable G)

/-- A metric relator row has no shorter positive cyclic period. -/
theorem row_rotation_aperiodic (hmetric : MetricSmallCancellation G length rows) (i : I) :
    RotationAperiodic (List.ofFn (rows i)) := by
  intro k hk hkl he
  have hkn : k < length i := by simpa using hkl
  let a : Origin length := ⟨i, true, 0⟩
  let b : Origin length := ⟨i, true, ⟨k, hkn⟩⟩
  have heq : a = b := by
    apply origin_eq_of_full_overlap G length rows hmetric a b le_rfl
    intro t ht
    have ht' : t < length i := ht
    have h := congrArg (fun l : List (Syllable G) ↦ l[t]?) he
    rw [List.getElem?_rotate (by simpa using ht)] at h
    simp only [List.length_ofFn, List.getElem?_ofFn] at h
    simp only [dite_eq_left ht', dite_eq_left (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))),
      Option.some.injEq] at h
    simp only [a, b, syllableAt, oriented, ite_true, zero_add]
    change rows i (Fin.ofNat (length i) t) = rows i (⟨k, hkn⟩ + (Fin.ofNat (length i) t))
    have hcast : (Fin.ofNat (length i) t) = ⟨t, ht'⟩ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt ht']
    simpa only [hcast, Fin.add_def, Nat.add_comm] using h.symm
  have hpos := congrArg (fun o : Origin length ↦ o.position.val) heq
  change 0 = k at hpos
  omega

/-- Every literal free lift of a metric relator is root-free. -/
theorem rowLift_rootFree (hmetric : MetricSmallCancellation G length rows) (i : I) :
    RootFree (rowLift G length rows i) := by
  let v := List.ofFn (rows i)
  have hv : v ≠ [] := by simp [v, List.ofFn_eq_nil_iff, NeZero.ne]
  have hp : RotationAperiodic (v.map (fun x ↦ (x, true))) := by
    intro k hk hkl he
    have hm := congrArg (List.map Prod.fst) he
    simp only [List.map_rotate, List.map_map, Function.comp_def] at hm
    exact row_rotation_aperiodic G length rows hmetric i k hk
      (by simpa [v] using hkl) (by simpa [v, Function.comp_def] using hm)
  have hr := rootFree_of_cyclicallyReduced_aperiodic
    (v.map (fun x ↦ (x, true))) (positiveWord_isCyclicallyReduced v)
    (by simpa using hv) hp
  rw [mk_positiveWord] at hr
  simpa [v, List.map_ofFn, Function.comp_def, rowLift] using hr

/-- Equal conjugates of an attaching row have equal images of their conjugators
in the actual lifted presentation quotient. -/
theorem rowLift_conjugator_image_eq (hmetric : MetricSmallCancellation G length rows)
    (i : I) (u v : FreeGroup (Σ a, G a))
    (h : u * rowLift G length rows i * u⁻¹ = v * rowLift G length rows i * v⁻¹) :
    quotient G (rowLift G length rows) u = quotient G (rowLift G length rows) v := by
  apply FreeGroupCentralizer.conjugator_image_eq (quotient G (rowLift G length rows))
    (rowLift_rootFree G length rows hmetric i) ?_ h
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)

end SmallPresentationStatements.RelativeSmallCancellation
