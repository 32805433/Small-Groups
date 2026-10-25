module

public import SmallPresentation.Seed.Interface
public import SmallPresentation.PackingConsequences
public import SmallPresentation.UniversalGroup.Embedding.Presentations

/-! # The abelianization of the literal thirteen-relator seed -/
public section

namespace SmallPresentationStatements.Seed

open UniversalGroup.Embedding

theorem inputRelator_commutative {n : ℕ} {G : Type*} [CommGroup G]
    (D : UniversalGroup.CodeWords) (w : UniversalGroup.BaseWords n)
    (f : Fin n → G) (i : Fin 2) :
    UniversalGroup.Word.eval f (UniversalGroup.inputRelator D w i) =
      (UniversalGroup.Word.eval f (w.u i))⁻¹ := by
  simp [UniversalGroup.inputRelator, mul_comm, mul_left_comm, mul_assoc]

theorem seed_row_six_commutative {G : Type*} [CommGroup G]
    (D : UniversalGroup.CodeWords) (c r : G) :
    UniversalGroup.Word.eval ![c, r] ((thirteenPresentation D).relator 6) = c⁻¹ := by
  change UniversalGroup.Word.eval ![c, r]
    (UniversalGroup.Word.substitute thirteenSubstitution
      (UniversalGroup.inputRelator D UniversalGroup.baseWords 0)) = c⁻¹
  simp [UniversalGroup.Word.eval_substitute,
    inputRelator_commutative, UniversalGroup.BaseWords.u, UniversalGroup.baseWords,
    thirteenSubstitution, thirteenWords, mul_comm, mul_left_comm, mul_assoc]

theorem seed_row_six_cyclic {G : Type*} [Group G]
    (D : UniversalGroup.CodeWords) (c : G) :
    UniversalGroup.Word.eval ![c, 1] ((thirteenPresentation D).relator 6) = c⁻¹ := by
  let f : Multiplicative ℤ →* G :=
    { toFun := fun z ↦ c ^ z.toAdd
      map_one' := by simp
      map_mul' := by intro x y; simp [zpow_add] }
  have h := congrArg f (seed_row_six_commutative D (Multiplicative.ofAdd 1) 1)
  rw [UniversalGroup.Word.map_eval, map_inv] at h
  have hf : (f ∘ ![Multiplicative.ofAdd 1, 1]) = ![c, 1] := by
    funext i
    fin_cases i <;> simp [f]
  rw [hf] at h
  simpa [f] using h

theorem seed_relators_kill_first {G : Type*} [Group G]
    (D : UniversalGroup.CodeWords) (r : G) (i : Fin 13) :
    UniversalGroup.Word.eval ![1, r] ((thirteenPresentation D).relator i) = 1 := by
  rw [thirteenPresentation_relator, UniversalGroup.Word.eval_substitute]
  have h : (fun j ↦ UniversalGroup.Word.eval ![1, r] (thirteenSubstitution j)) =
      fun _ : Fin 6 ↦ (1 : G) := by
    funext j
    fin_cases j <;> simp [thirteenSubstitution, thirteenWords]
  rw [h]
  simp [UniversalGroup.Word.eval, FreeGroup.lift_mk]

theorem seed_normalGenerator (D : UniversalGroup.CodeWords) :
    Subgroup.normalClosure
      ({PresentedGroup.of (rels := (fromUpstream (thirteenPresentation D)).relSet) 1} :
        Set (fromUpstream (thirteenPresentation D)).Group) = ⊤ := by
  apply normalGenerator_of_relator_collapse (fromUpstream (thirteenPresentation D)) 6
  intro H _ f hf hr
  have hv : f = ![f 0, 1] := by
    funext i
    fin_cases i <;> simp [hf]
  rw [hv] at hr
  change UniversalGroup.Word.eval ![f 0, 1] ((thirteenPresentation D).relator 6) = 1 at hr
  rw [seed_row_six_cyclic] at hr
  exact inv_eq_one.mp hr

def seed_character (D : UniversalGroup.CodeWords) :
    (fromUpstream (thirteenPresentation D)).Group →* Multiplicative ℤ :=
  (thirteenPresentation D).homOfRelators ![1, Multiplicative.ofAdd 1]
    (seed_relators_kill_first D (Multiplicative.ofAdd 1))

@[simp] theorem seed_character_second (D : UniversalGroup.CodeWords) :
    seed_character D (PresentedGroup.of 1) = Multiplicative.ofAdd 1 := by
  exact (thirteenPresentation D).homOfRelators_of ![1, Multiplicative.ofAdd 1]
    (seed_relators_kill_first D (Multiplicative.ofAdd 1)) 1

/-- The seed's actual abelianization is infinite cyclic for every coding datum. -/
theorem seed_abelianization (D : UniversalGroup.CodeWords) :
    Nonempty (Abelianization (fromUpstream (thirteenPresentation D)).Group ≃*
      Multiplicative ℤ) :=
  abelianization_Z_of_normalGenerator _ (seed_normalGenerator D)
    (seed_character D) (seed_character_second D)

end SmallPresentationStatements.Seed
