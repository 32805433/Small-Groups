module

public import SmallPresentation.IdentitySequences

/-!
# Quotients by lifted relators

For a surjective presentation map, quotienting by new relators is canonically
equivalent to quotienting the source by both its old relations and chosen new lifts.
The equivalence records the actual quotient maps and requires no finite presentation.
-/
@[expose] public section

namespace SmallPresentationStatements.QuotientRelatorLifts

open RelationCoordinates

variable {E F O I : Type} [Group E] [Group F]
    (p : E →* F) (hp : Function.Surjective p) (old : O → E)
    (hker : p.ker = Relations old) (new : I → E)

abbrev liftedRelations := Relations (Sum.elim old new)
abbrev targetRelations := Relations (fun i ↦ p (new i))
abbrev Lifted := E ⧸ liftedRelations old new
abbrev Target := F ⧸ targetRelations p new

/-- The old relations are among the lifted presentation's relations. -/
theorem old_le_lifted : Relations old ≤ liftedRelations old new := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨o, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inl o, rfl⟩

/-- The map from the base group into the quotient by the lifted relations. -/
noncomputable def baseLift : F →* Lifted old new :=
  p.liftOfSurjective hp ⟨QuotientGroup.mk' (liftedRelations old new), by
    rw [QuotientGroup.ker_mk', hker]
    exact old_le_lifted old new⟩

@[simp] theorem baseLift_apply (e : E) :
    baseLift p hp old hker new (p e) = QuotientGroup.mk' (liftedRelations old new) e :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The quotient map induced by the chosen lifted presentation. -/
noncomputable def toLifted : Target p new →* Lifted old new :=
  QuotientGroup.lift (targetRelations p new) (baseLift p hp old hker new) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    change baseLift p hp old hker new (p (new i)) = 1
    rw [baseLift_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩))

/-- The reverse map applies the presentation map and then imposes the new relators. -/
def fromLifted : Lifted old new →* Target p new :=
  QuotientGroup.lift (liftedRelations old new)
    ((QuotientGroup.mk' (targetRelations p new)).comp p) (by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨o | i, rfl⟩
      · have ho : p (old o) = 1 := by
          have hm : old o ∈ Relations old := Subgroup.subset_normalClosure ⟨o, rfl⟩
          rw [← hker] at hm
          exact hm
        change QuotientGroup.mk' (targetRelations p new) (p (old o)) = 1
        rw [ho, map_one]
      · change QuotientGroup.mk' (targetRelations p new) (p (new i)) = 1
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩))

@[simp] theorem fromLifted_mk (e : E) :
    fromLifted p old hker new (QuotientGroup.mk' (liftedRelations old new) e) =
      QuotientGroup.mk' (targetRelations p new) (p e) := rfl

@[simp] theorem toLifted_mk (f : F) :
    toLifted p hp old hker new (QuotientGroup.mk' (targetRelations p new) f) =
      baseLift p hp old hker new f := rfl

/-- The canonical equivalence between the actual base quotient and the lifted presentation. -/
noncomputable def equiv : Target p new ≃* Lifted old new where
  toFun := toLifted p hp old hker new
  invFun := fromLifted p old hker new
  left_inv x := by
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (targetRelations p new) x
    obtain ⟨e, rfl⟩ := hp f
    rw [toLifted_mk, baseLift_apply, fromLifted_mk]
  right_inv x := by
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (liftedRelations old new) x
    rw [fromLifted_mk, toLifted_mk, baseLift_apply]
  map_mul' := map_mul _

@[simp] theorem equiv_mk (f : F) :
    equiv p hp old hker new (QuotientGroup.mk' (targetRelations p new) f) =
      baseLift p hp old hker new f := rfl

@[simp] theorem equiv_symm_mk (e : E) :
    (equiv p hp old hker new).symm (QuotientGroup.mk' (liftedRelations old new) e) =
      QuotientGroup.mk' (targetRelations p new) (p e) := rfl

end SmallPresentationStatements.QuotientRelatorLifts
