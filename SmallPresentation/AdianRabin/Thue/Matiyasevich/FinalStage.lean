module

public import SmallPresentation.UniversalGroup.Coding.Thue.FinalStage

/-
Ported from `GroupUndecidability/Thue/Matiyasevich/FinalStage.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.Matiyasevich.Reduction

@[expose] public section

namespace UniversalGroup

namespace Thue

namespace Matiyasevich1993

/-! ## Section 2.5: `T₂` to the final binary three-rule system -/

theorem rho₂_computable : Computable rho₂ :=
  (list_flatMap_primrec_of_finite rho₂Letter).to_comp

theorem phi₂_context_rho₂ (l : List (Fin 2)) (X Y : List A₂) :
    phi₂ (l ++ rho₂ X ++ rho₂ Y) = phi₂ l ++ X ++ Y := by
  calc
    phi₂ (l ++ rho₂ X ++ rho₂ Y) =
        phi₂ (l ++ (rho₂ X ++ rho₂ Y)) := by rw [List.append_assoc]
    _ = phi₂ (l ++ rho₂ (X ++ Y)) := by rw [rho₂_append]
    _ = phi₂ l ++ (X ++ Y) := phi₂_append_rho₂ l (X ++ Y)
    _ = phi₂ l ++ X ++ Y := by rw [List.append_assoc]

theorem phi₂_context_of_encoded_block (l block : List (Fin 2))
    (X Y : List A₂) (hblock : block = rho₂ X) :
    phi₂ (l ++ block ++ rho₂ Y) = phi₂ l ++ X ++ Y := by
  subst block
  exact phi₂_context_rho₂ l X Y

theorem fin₃_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  omega

theorem base_rule_step (U V : List (Fin 2)) (i : Fin 3)
    (l r : List (Fin 2)) :
    ThueStep (baseSystem U V)
      (l ++ baseF U i ++ r) (l ++ baseE V i ++ r) :=
  ⟨l, r, baseF U i, baseE V i, ⟨i, rfl⟩,
    Or.inl ⟨rfl, rfl⟩⟩

/-- Each of the five rules of `T₂` is simulated by the final three rules.
The middle two housekeeping simulations use the first or second final rule in
a one-letter right context. -/
theorem rho₂_rule (L M : List A₂) (i : Fin 5) :
    ThueEq (baseSystem (rho₂ L) (rho₂ M))
      (rho₂ (stage₂F L i)) (rho₂ (stage₂E M i)) := by
  fin_cases i
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE, FinalLetters.a, FinalLetters.b, FinalLetters.e] using
        base_rule_step (rho₂ L) (rho₂ M) 1 [] [])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE, FinalLetters.a, FinalLetters.b, FinalLetters.e] using
        base_rule_step (rho₂ L) (rho₂ M) 1 [] [(0 : Fin 2)])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE, FinalLetters.a, FinalLetters.b, FinalLetters.e] using
        base_rule_step (rho₂ L) (rho₂ M) 0 [] [])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE, FinalLetters.a, FinalLetters.b, FinalLetters.e] using
        base_rule_step (rho₂ L) (rho₂ M) 0 [] [(0 : Fin 2)])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE, FinalLetters.a, FinalLetters.b, FinalLetters.e] using
        base_rule_step (rho₂ L) (rho₂ M) 2 [] [])

/-- Forward half of equivalence (10) for the last stage. -/
theorem rho₂_step (L M : List A₂) {X Y : List A₂}
    (h : ThueStep (stage₂System L M) X Y) :
    ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, h⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [rho₂_append] using
      thueEq_context (rho₂ l) (rho₂ r) (rho₂_rule L M i)
  · simpa only [rho₂_append] using
      thueEq_context (rho₂ l) (rho₂ r) (thueEq_symm (rho₂_rule L M i))

/-- Forward half of equivalence (10) for arbitrary derivations. -/
theorem rho₂_forward (L M : List A₂) {X Y : List A₂}
    (h : ThueEq (stage₂System L M) X Y) :
    ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (rho₂_step L M hbc)

/-- Every nonempty `T₂` word has nonempty binary encoding. -/
theorem rho₂_ne_nil {W : List A₂} (hW : W ≠ []) : rho₂ W ≠ [] := by
  cases W with
  | nil => contradiction
  | cons x W =>
      fin_cases x <;> simp [rho₂, rho₂Letter]

theorem stage₂_rule_step (L M : List A₂) (i : Fin 5)
    (l r : List A₂) :
    ThueStep (stage₂System L M)
      (l ++ stage₂F L i ++ r) (l ++ stage₂E M i ++ r) :=
  ⟨l, r, stage₂F L i, stage₂E M i, ⟨i, rfl⟩,
    Or.inl ⟨rfl, rfl⟩⟩

/-- A use of either short final relation always decodes to one of the four
housekeeping relations (20)--(23).  Which one is selected is determined by the
single residual `d` at the beginning of the right context. -/
theorem phi₂_short_rule (L M : List A₂) (i : Fin 3) (hi : i ≠ 2)
    (l r : List (Fin 2)) :
    ThueEq (stage₂System L M)
      (phi₂ (l ++ baseF (rho₂ L) i ++ r))
      (phi₂ (l ++ baseE (rho₂ M) i ++ r)) := by
  rcases rho₂_phi₂_reconstruct r with hr | hr
  · rcases fin₃_cases i with hi0 | hi1 | hi2
    · have hF : baseF (rho₂ L) 0 = rho₂ [FinalLetters.e, FinalLetters.b, FinalLetters.a] := by
        simp [baseF, rho₂, rho₂Letter, FinalLetters.a, FinalLetters.b, FinalLetters.e]
      have hE : baseE (rho₂ M) 0 = rho₂ [FinalLetters.a, FinalLetters.e] := by
        simp [baseE, rho₂, rho₂Letter, FinalLetters.a, FinalLetters.e]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 0) [FinalLetters.e, FinalLetters.b, FinalLetters.a] (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 0) [FinalLetters.a, FinalLetters.e] (phi₂ r) hE
      rw [hr] at hleft hright
      rw [hleft, hright]
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 2 (phi₂ l) (phi₂ r))
    · have hF : baseF (rho₂ L) 1 = rho₂ [FinalLetters.e, FinalLetters.a, FinalLetters.a] := by
        simp [baseF, rho₂, rho₂Letter, FinalLetters.a, FinalLetters.e]
      have hE : baseE (rho₂ M) 1 = rho₂ [FinalLetters.a, FinalLetters.e] := by
        simp [baseE, rho₂, rho₂Letter, FinalLetters.a, FinalLetters.e]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 1) [FinalLetters.e, FinalLetters.a, FinalLetters.a] (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 1) [FinalLetters.a, FinalLetters.e] (phi₂ r) hE
      rw [hr] at hleft hright
      rw [hleft, hright]
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 0 (phi₂ l) (phi₂ r))
    · subst i
      exact (hi rfl).elim

  · rcases fin₃_cases i with hi0 | hi1 | hi2
    · have hF : baseF (rho₂ L) 0 ++ [(0 : Fin 2)] = rho₂ [FinalLetters.e, FinalLetters.b, FinalLetters.b] := by
        simp [baseF, rho₂, rho₂Letter, FinalLetters.b, FinalLetters.e]
      have hE : baseE (rho₂ M) 0 ++ [(0 : Fin 2)] = rho₂ [FinalLetters.b, FinalLetters.e] := by
        simp [baseE, rho₂, rho₂Letter, FinalLetters.b, FinalLetters.e]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 0 ++ [(0 : Fin 2)]) [FinalLetters.e, FinalLetters.b, FinalLetters.b] (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 0 ++ [(0 : Fin 2)]) [FinalLetters.b, FinalLetters.e] (phi₂ r) hE
      have hleft' :
          phi₂ (l ++ baseF (rho₂ L) 0 ++ r) =
            phi₂ l ++ [FinalLetters.e, FinalLetters.b, FinalLetters.b] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseF (rho₂ L) 0 ++ r) =
              phi₂ (l ++ baseF (rho₂ L) 0 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseF (rho₂ L) 0 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [FinalLetters.e, FinalLetters.b, FinalLetters.b] ++ phi₂ r := hleft
      have hright' :
          phi₂ (l ++ baseE (rho₂ M) 0 ++ r) =
            phi₂ l ++ [FinalLetters.b, FinalLetters.e] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseE (rho₂ M) 0 ++ r) =
              phi₂ (l ++ baseE (rho₂ M) 0 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseE (rho₂ M) 0 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [FinalLetters.b, FinalLetters.e] ++ phi₂ r := hright
      rw [hleft', hright']
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 3 (phi₂ l) (phi₂ r))
    · have hF : baseF (rho₂ L) 1 ++ [(0 : Fin 2)] = rho₂ [FinalLetters.e, FinalLetters.a, FinalLetters.b] := by
        simp [baseF, rho₂, rho₂Letter, FinalLetters.a, FinalLetters.b, FinalLetters.e]
      have hE : baseE (rho₂ M) 1 ++ [(0 : Fin 2)] = rho₂ [FinalLetters.b, FinalLetters.e] := by
        simp [baseE, rho₂, rho₂Letter, FinalLetters.b, FinalLetters.e]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 1 ++ [(0 : Fin 2)]) [FinalLetters.e, FinalLetters.a, FinalLetters.b] (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 1 ++ [(0 : Fin 2)]) [FinalLetters.b, FinalLetters.e] (phi₂ r) hE
      have hleft' :
          phi₂ (l ++ baseF (rho₂ L) 1 ++ r) =
            phi₂ l ++ [FinalLetters.e, FinalLetters.a, FinalLetters.b] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseF (rho₂ L) 1 ++ r) =
              phi₂ (l ++ baseF (rho₂ L) 1 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseF (rho₂ L) 1 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [FinalLetters.e, FinalLetters.a, FinalLetters.b] ++ phi₂ r := hleft
      have hright' :
          phi₂ (l ++ baseE (rho₂ M) 1 ++ r) =
            phi₂ l ++ [FinalLetters.b, FinalLetters.e] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseE (rho₂ M) 1 ++ r) =
              phi₂ (l ++ baseE (rho₂ M) 1 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseE (rho₂ M) 1 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [FinalLetters.b, FinalLetters.e] ++ phi₂ r := hright
      rw [hleft', hright']
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 1 (phi₂ l) (phi₂ r))
    · subst i
      exact (hi rfl).elim

/-- The long final relation also decodes directly when the right context is
aligned.  Thus the only unformalized case in the last-stage converse is the
long relation together with the residual alternative
`0 :: rho₂ (phi₂ r) = r`. -/
theorem phi₂_long_rule_aligned (L M : List A₂)
    (l r : List (Fin 2)) (hr : rho₂ (phi₂ r) = r) :
    ThueEq (stage₂System L M)
      (phi₂ (l ++ baseF (rho₂ L) 2 ++ r))
      (phi₂ (l ++ baseE (rho₂ M) 2 ++ r)) := by
  have hleft := phi₂_context_of_encoded_block l
    (baseF (rho₂ L) 2) L (phi₂ r) (by simp [baseF])
  have hright := phi₂_context_of_encoded_block l
    (baseE (rho₂ M) 2) M (phi₂ r) (by simp [baseE])
  rw [hr] at hleft hright
  rw [hleft, hright]
  exact Relation.ReflTransGen.single
    (stage₂_rule_step L M 4 (phi₂ l) (phi₂ r))

/-- The exact reachability invariant needed to rule out the bad long-rule
alignment on pages 50--52. -/
def LongRuleAlignedFrom (L M X : List A₂) : Prop :=
  ∀ W, ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W →
    ∀ l r,
      (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r

theorem phi₂_step_of_long_aligned (L M : List A₂)
    {X Y : List (Fin 2)}
    (haligned : ∀ l r,
      (X = l ++ rho₂ L ++ r ∨ X = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r)
    (h : ThueStep (baseSystem (rho₂ L) (rho₂ M)) X Y) :
    ThueEq (stage₂System L M) (phi₂ X) (phi₂ Y) := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hXY⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases fin₃_cases i with hi0 | hi1 | hi2
  · subst i
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact phi₂_short_rule L M 0 (by decide) l r
    · exact thueEq_symm (phi₂_short_rule L M 0 (by decide) l r)
  · subst i
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact phi₂_short_rule L M 1 (by decide) l r
    · exact thueEq_symm (phi₂_short_rule L M 1 (by decide) l r)
  · subst i
    rcases hXY with ⟨hX, rfl⟩ | ⟨hX, rfl⟩
    · have hr := haligned l r (Or.inl (by simpa [baseF] using hX))
      rw [hX]
      simpa [baseF, baseE] using phi₂_long_rule_aligned L M l r hr
    · have hr := haligned l r (Or.inr (by simpa [baseE] using hX))
      rw [hX]
      simpa [baseF, baseE] using
        thueEq_symm (phi₂_long_rule_aligned L M l r hr)

/-- Conditional converse for the final stage.  The rewriting and decoder
bookkeeping reduce precisely to `LongRuleAlignedFrom`, supplied by the
`e`-count and priority-normal-form invariants of Section 2.4. -/
theorem rho₂_reflect_of_longRuleAligned (L M X Y : List A₂)
    (hsafe : LongRuleAlignedFrom L M X)
    (h : ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y)) :
    ThueEq (stage₂System L M) X Y := by
  have aux : ∀ {W : List (Fin 2)},
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W →
      ThueEq (stage₂System L M) X (phi₂ W) := by
    intro W hW
    induction hW with
    | refl =>
        rw [phi₂_rho₂]
        exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact ih.trans (phi₂_step_of_long_aligned L M
          (fun l r hocc => hsafe _ hab l r hocc) hbc)
  simpa using aux h

theorem rho₂_iff_of_longRuleAligned (L M X : List A₂)
    (hsafe : LongRuleAlignedFrom L M X) (Y : List A₂) :
    ThueEq (stage₂System L M) X Y ↔
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) :=
  ⟨rho₂_forward L M,
    rho₂_reflect_of_longRuleAligned L M X Y hsafe⟩

end Matiyasevich1993

end Thue

end UniversalGroup
