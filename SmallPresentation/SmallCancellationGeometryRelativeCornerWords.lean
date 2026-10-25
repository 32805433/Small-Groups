module

public import SmallPresentation.SmallCancellationGeometryCornerCancellation
public import SmallPresentation.SmallCancellationGeometryRelativeFaces

/-!
# Exact recorded words under adjacent-corner cancellation

The surviving rotation skips the two consecutive deleted incidences. Assigning their
recorded blocks to the preceding surviving incidence preserves every surviving based
vertex word. This statement concerns actual incidence words, independently of coefficients
or region equations.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

open PermutationCycles

variable {D Z : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

open Classical in
/-- Accumulate the deleted pair at the preceding surviving incidence. -/
noncomputable def blocks (block : D → List Z) (d : C.Dart) : List Z :=
  block d.val ++ if P.rotation d.val = C.left then block C.left ++ block C.right else []

/-- The successor beyond a deleted pair survives whenever the predecessor survives. -/
theorem after_survives (d : C.Dart) (h : P.rotation d.val = C.left) :
    P.rotation C.right ≠ C.left ∧ P.rotation C.right ≠ C.right := by
  constructor
  · intro he
    exact d.property.2 (P.rotation.injective (h.trans he.symm))
  · intro he
    exact C.ne (P.rotation.injective (C.next.trans he.symm))

open Classical in
/-- Any walk between surviving endpoints has the precise filtered departure word, and
concatenating recorded blocks restores its entire original departure word. -/
theorem delete_walk (block : D → List Z) {d e : D} {l : List D}
    (h : Walk P.rotation d e l)
    (hd : d ≠ C.left ∧ d ≠ C.right) (he : e ≠ C.left ∧ e ≠ C.right) :
    ∃ l' : List C.Dart,
      Walk C.delete.rotation ⟨d, hd⟩ ⟨e, he⟩ l' ∧
      l'.map Subtype.val = l.filter (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) ∧
      l'.flatMap (C.blocks block) = l.flatMap block := by
  classical
  cases h with
  | nil d => exact ⟨[], .nil _, rfl, rfl⟩
  | cons d e rest ht =>
    by_cases hn : P.rotation d = C.left
    · cases ht with
      | nil => exact False.elim (he.1 hn)
      | cons _ _ rest ht =>
        have ht' : Walk P.rotation C.right e rest := by simpa only [hn, C.next] using ht
        cases ht' with
        | nil => exact False.elim (he.2 rfl)
        | cons _ _ rest htail =>
          have hs := C.after_survives ⟨d, hd⟩ hn
          obtain ⟨out, hw, hm, hb⟩ := delete_walk block htail hs he
          let first : C.Dart := ⟨d, hd⟩
          have hstep : C.delete.rotation first = ⟨P.rotation C.right, hs⟩ := by
            apply Subtype.ext
            simp only [C.rotation_val, first, hn, ite_true]
          refine ⟨first :: out, ?_, ?_, ?_⟩
          · apply Walk.cons
            rw [hstep]
            exact hw
          · simp [List.map_cons, first, hm, hd, hn, C.ne]
          · simp [List.flatMap_cons, blocks, first, hn, hb, List.append_assoc]
    · have hs : P.rotation d ≠ C.left ∧ P.rotation d ≠ C.right := by
        refine ⟨hn, ?_⟩
        intro hh
        exact hd.1 (P.rotation.injective (hh.trans C.next.symm))
      obtain ⟨out, hw, hm, hb⟩ := delete_walk block ht hs he
      let first : C.Dart := ⟨d, hd⟩
      have hstep : C.delete.rotation first = ⟨P.rotation d, hs⟩ := by
        apply Subtype.ext
        simp only [C.rotation_val, first, hn, ite_false]
      refine ⟨first :: out, ?_, ?_, ?_⟩
      · apply Walk.cons
        rw [hstep]
        exact hw
      · simp [List.map_cons, first, hm, hd]
      · simp [List.flatMap_cons, blocks, first, hn, hb]
termination_by l.length

/-- Exact original block words on every surviving based vertex. -/
theorem vertex_blocks [Finite D] (block : D → List Z) (d : C.Dart) :
    (C.delete.vertexBoundary d).flatMap (C.blocks block) =
      (P.vertexBoundary d.val).flatMap block := by
  classical
  obtain ⟨l, hw, hm, hb⟩ := C.delete_walk block
    (cycleBoundary_walk P.rotation d.val) d.property d.property
  have hnd : l.Nodup := by
    apply List.Nodup.of_map
    rw [hm]
    exact (cycleBoundary_nodup P.rotation d.val).filter _
  have hn : l ≠ [] := by
    intro hl
    have hself : d.val ∈ (cycleBoundary P.rotation d.val).filter
        (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
      simp [mem_cycleBoundary_self, d.property]
    rw [← hm, hl] at hself
    exact List.not_mem_nil hself
  have hl := hw.eq_cycleBoundary hn hnd
  rw [hl] at hb
  exact hb

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
