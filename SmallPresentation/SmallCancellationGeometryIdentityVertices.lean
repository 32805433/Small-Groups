module

public import SmallPresentation.SmallCancellationGeometryIdentityRibbon

/-!
# Original relator occurrences are exactly the cycles of the constructed vertex rotation

The cyclic order and reading are checked on actual indexed corners. Distinct occurrence
indices never merge, even when their labels and values agree. Empty rows have no incident
vertices; all nonempty rows contribute exactly one vertex cycle.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I : Type} (rows : I → List (SignedLetter X))

instance discDartsFintype (s : Peiffer.Sequence (FreeGroup X) I) : Fintype (DiscDarts rows s) := by
  induction s with
  | nil => exact inferInstanceAs (Fintype (Fin 0))
  | cons a s ih =>
    let := ih
    exact inferInstanceAs (Fintype (Fin (orientedWord (rows a.1.2) a.2).length ⊕ DiscDarts rows s))

/-- Distinct corners on a prescribed relator occurrence remain distinct darts. -/
theorem discAt_injective (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length) :
    Function.Injective (discAt rows s i) := by
  intro d e he
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    induction i using Fin.cases with
    | zero => exact Sum.inl.inj he
    | succ i => exact ih i (Sum.inr.inj he)

/-- Every retained relator dart has an original occurrence and a unique local corner. -/
theorem exists_discAt (s : Peiffer.Sequence (FreeGroup X) I) (d : DiscDarts rows s) :
    ∃ (i : Fin s.length) (j : Fin (orientedWord (rows s[i].1.2) s[i].2).length),
      discAt rows s i j = d := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · exact ⟨0, d, rfl⟩
    · obtain ⟨i, j, he⟩ := ih d
      exact ⟨i.succ, j, congrArg Sum.inr he⟩

/-- The typed incidence set is exactly the dependent sum of the original row corners. -/
noncomputable def discCornerEquiv (s : Peiffer.Sequence (FreeGroup X) I) :
    (Σ i : Fin s.length, Fin (orientedWord (rows s[i].1.2) s[i].2).length) ≃ DiscDarts rows s :=
  Equiv.ofBijective (fun d ↦ discAt rows s d.1 d.2) (by
    constructor
    · rintro ⟨i, d⟩ ⟨j, e⟩ he
      have hij := congrArg (discOccurrence rows s) he
      simp only [discOccurrence_at] at hij
      subst j
      exact congrArg (Sigma.mk i) (discAt_injective rows s i he)
    · intro d
      obtain ⟨i, j, he⟩ := exists_discAt rows s d
      exact ⟨⟨i, j⟩, he⟩)

/-- Traversing the vertex permutation is literal iteration of successor on the original row. -/
theorem discRotation_iterate_at (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length) (n : ℕ) :
    (discRotation rows s)^[n] (discAt rows s i d) =
      discAt rows s i ((finRotate (orientedWord (rows s[i].1.2) s[i].2).length)^[n] d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, discRotation_at,
      Function.iterate_succ_apply']

/-- Distinct corners of one original row lie on the same actual vertex cycle. -/
theorem discAt_sameCycle (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d e : Fin (orientedWord (rows s[i].1.2) s[i].2).length) :
    (discRotation rows s).SameCycle (discAt rows s i d) (discAt rows s i e) := by
  let : NeZero (orientedWord (rows s[i].1.2) s[i].2).length := d.neZero
  let k := e - d
  refine ⟨(k.val : ℤ), ?_⟩
  rw [zpow_natCast, Equiv.Perm.coe_pow, discRotation_iterate_at, ← finCycle_eq_finRotate_iterate]
  simp [finCycle_apply, k]

/-- Iterating the prescribed rotation never changes its original occurrence. -/
theorem discOccurrence_iterate (s : Peiffer.Sequence (FreeGroup X) I)
    (d : DiscDarts rows s) (n : ℕ) :
    discOccurrence rows s ((discRotation rows s)^[n] d) = discOccurrence rows s d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', discOccurrence_rotation, ih]

/-- Two darts belong to the same vertex exactly when their original occurrence indices agree. -/
theorem disc_sameCycle_iff (s : Peiffer.Sequence (FreeGroup X) I) (d e : DiscDarts rows s) :
    (discRotation rows s).SameCycle d e ↔ discOccurrence rows s d = discOccurrence rows s e := by
  constructor
  · intro he
    obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow, discOccurrence_iterate]
  · intro he
    obtain ⟨i, j, rfl⟩ := exists_discAt rows s d
    obtain ⟨k, l, rfl⟩ := exists_discAt rows s e
    simp only [discOccurrence_at] at he
    subst k
    exact discAt_sameCycle rows s i j l

/-- Occurrences which have an actual boundary incidence. Empty rows remain recorded
in the original sequence but do not produce a permutation cycle. -/
abbrev ActiveOccurrence (s : Peiffer.Sequence (FreeGroup X) I) :=
  {i : Fin s.length // 0 < (orientedWord (rows s[i].1.2) s[i].2).length}

theorem discOccurrence_pos (s : Peiffer.Sequence (FreeGroup X) I) (d : DiscDarts rows s) :
    0 < (orientedWord (rows s[discOccurrence rows s d].1.2)
      s[discOccurrence rows s d].2).length := by
  obtain ⟨i, j, rfl⟩ := exists_discAt rows s d
  simpa only [discOccurrence_at] using j.pos

/-- Send an actual vertex cycle to its original nonempty relator occurrence. -/
def vertexOccurrence (s : Peiffer.Sequence (FreeGroup X) I) :
    Quotient (Equiv.Perm.SameCycle.setoid (discRotation rows s)) → ActiveOccurrence rows s :=
  Quotient.lift (fun d ↦ ⟨discOccurrence rows s d, discOccurrence_pos rows s d⟩)
    (fun d e he ↦ Subtype.ext ((disc_sameCycle_iff rows s d e).mp he))

theorem vertexOccurrence_bijective (s : Peiffer.Sequence (FreeGroup X) I) :
    Function.Bijective (vertexOccurrence rows s) := by
  constructor
  · intro v w
    induction v using Quotient.inductionOn with
    | h d =>
      induction w using Quotient.inductionOn with
      | h e =>
        intro he
        apply Quotient.sound
        exact (disc_sameCycle_iff rows s d e).mpr (congrArg Subtype.val he)
  · rintro ⟨i, hi⟩
    refine ⟨Quotient.mk _ (discAt rows s i ⟨0, hi⟩), ?_⟩
    apply Subtype.ext
    exact discOccurrence_at rows s i ⟨0, hi⟩

/-- Exactly one actual vertex cycle is contributed by each nonempty original row. -/
noncomputable def discVertexEquiv (s : Peiffer.Sequence (FreeGroup X) I) :
    Quotient (Equiv.Perm.SameCycle.setoid (discRotation rows s)) ≃ ActiveOccurrence rows s :=
  Equiv.ofBijective _ (vertexOccurrence_bijective rows s)

/-- Reading all marked corners yields the exact signed row, not only a cyclic conjugate. -/
theorem disc_row_read (paths : WordSection X) (s : Peiffer.Sequence (FreeGroup X) I)
    (i : Fin s.length) :
    List.ofFn (fun d : Fin (orientedWord (rows s[i].1.2) s[i].2).length ↦
      discRead paths rows s (discAt rows s i d)) = orientedWord (rows s[i].1.2) s[i].2 := by
  simp only [discRead_at]
  exact List.ofFn_get _

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
