module

public import SmallPresentation.SmallCancellationGeometryBigon

/-!
# Word blocks under contraction of permutation walks

A suppressed edge may carry an entire block of original relator incidences. Bypassing a dart
concatenates its block with its predecessor's block. This operation preserves the actual word
read by every walk whose endpoints survive; it does not assume that blocks are single letters.
-/
@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D Y : Type*}

/-- A finite walk records each departing dart, excluding its final endpoint. -/
inductive Walk (σ : Equiv.Perm D) : D → D → List D → Prop
  | nil (d) : Walk σ d d []
  | cons (d e l) : Walk σ (σ d) e l → Walk σ d e (d :: l)

namespace Walk

/-- Starting a walk at a point not in its departure list forces it to be empty. -/
theorem nil_of_not_mem {σ : Equiv.Perm D} {d e : D} {l : List D}
    (h : Walk σ d e l) (hd : d ∉ l) : l = [] := by
  cases h with
  | nil => rfl
  | cons => exact False.elim (hd List.mem_cons_self)

/-- The endpoint of a permutation walk is its corresponding iterate. -/
theorem endpoint {σ : Equiv.Perm D} {d e : D} {l : List D}
    (h : Walk σ d e l) : σ^[l.length] d = e := by
  induction h with
  | nil => rfl
  | cons d e l _ ih => simpa only [List.length_cons, Function.iterate_succ_apply] using ih

/-- Every recorded departure is the corresponding iterate of the starting point. -/
theorem departures {σ : Equiv.Perm D} {d e : D} {l : List D}
    (h : Walk σ d e l) : l = List.ofFn (fun k : Fin l.length ↦ σ^[k.val] d) := by
  induction h with
  | nil => simp
  | cons d e l _ ih =>
    rw [List.length_cons, List.ofFn_succ]
    simp only [Fin.val_zero, Function.iterate_zero, id_eq, Fin.val_succ,
      Function.iterate_succ_apply]
    exact congrArg (List.cons d) ih

/-- Every finite iterate segment is a permutation walk. -/
theorem of_iterate (σ : Equiv.Perm D) (n : ℕ) (d : D) :
    Walk σ d (σ^[n] d) (List.ofFn (fun k : Fin n ↦ σ^[k.val] d)) := by
  induction n generalizing d with
  | zero => simpa using Walk.nil (σ := σ) d
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Function.iterate_zero, id_eq, Fin.val_succ,
      Function.iterate_succ_apply]
    exact Walk.cons d _ _ (ih (σ d))

/-- A nonempty closed walk with distinct departures traverses its cycle exactly once. -/
theorem length_eq_minimalPeriod {σ : Equiv.Perm D} {d : D} {l : List D}
    (h : Walk σ d d l) (hn : l ≠ []) (hnd : l.Nodup) :
    l.length = Function.minimalPeriod σ d := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hn
  have hp : Function.IsPeriodicPt σ l.length d := h.endpoint
  have hmin := hp.minimalPeriod_le hpos
  have hmpos := hp.minimalPeriod_pos hpos
  apply Nat.le_antisymm _ hmin
  by_contra hle
  have hlt : Function.minimalPeriod σ d < l.length := by omega
  rw [h.departures] at hnd
  have hi := List.nodup_ofFn.mp hnd
  have hz : (⟨0, hpos⟩ : Fin l.length) = ⟨Function.minimalPeriod σ d, hlt⟩ := by
    apply hi
    simp
  have hv := congrArg Fin.val hz
  change 0 = Function.minimalPeriod σ d at hv
  omega

end Walk

/-- Concatenate the removed block with its predecessor's block. -/
noncomputable def contractBlock (σ : Equiv.Perm D) (a : D) (block : D → List Y)
    (d : {d : D // d ≠ a}) : List Y := by
  classical
  exact block d.val ++ if σ d.val = a then block a else []

/-- Nonempty old blocks remain nonempty after contraction. -/
theorem contractBlock_nonempty (σ : Equiv.Perm D) (a : D) (block : D → List Y)
    (hblock : ∀ d, block d ≠ []) (d : {d : D // d ≠ a}) :
    contractBlock σ a block d ≠ [] := by
  classical
  simp [contractBlock, hblock d.val]

open Classical in
/-- Bypassing a non-fixed dart preserves the entire concatenated word along any finite walk.
The new departure list consists exactly of the surviving old departures in their old order. -/
theorem contract_walk (σ : Equiv.Perm D) (a : D) (ha : σ a ≠ a) (block : D → List Y)
    {d e : D} {l : List D} (h : Walk σ d e l) (hd : d ≠ a) (he : e ≠ a) :
    ∃ l' : List {d : D // d ≠ a},
      Walk (contract σ a) ⟨d, hd⟩ ⟨e, he⟩ l' ∧
      l'.map Subtype.val = l.filter (fun x ↦ decide (x ≠ a)) ∧
      l'.flatMap (contractBlock σ a block) = l.flatMap block := by
  classical
  cases h with
  | nil d => exact ⟨[], .nil _, rfl, rfl⟩
  | cons d e rest ht =>
    by_cases hnext : σ d = a
    · cases ht with
      | nil => exact False.elim (he hnext)
      | cons _ _ rest ht =>
        have ht' : Walk σ (σ a) e rest := by simpa only [hnext] using ht
        obtain ⟨out, hw, hm, hb⟩ := contract_walk σ a ha block ht' ha he
        let first : {d : D // d ≠ a} := ⟨d, hd⟩
        have hs : contract σ a first = ⟨σ a, ha⟩ :=
          Subtype.ext (contract_val_eq σ a first hnext)
        refine ⟨first :: out, ?_, ?_, ?_⟩
        · apply Walk.cons
          rw [show contract σ a ⟨d, hd⟩ = ⟨σ a, ha⟩ from hs]
          exact hw
        · simp [List.map_cons, first, hm, hd, hnext]
        · simp [List.flatMap_cons, contractBlock, first, hnext, hb, List.append_assoc]
    · obtain ⟨out, hw, hm, hb⟩ := contract_walk σ a ha block ht hnext he
      let first : {d : D // d ≠ a} := ⟨d, hd⟩
      have hs : contract σ a first = ⟨σ d, hnext⟩ :=
        Subtype.ext (contract_val_ne σ a first hnext)
      refine ⟨first :: out, ?_, ?_, ?_⟩
      · apply Walk.cons
        rw [show contract σ a ⟨d, hd⟩ = ⟨σ d, hnext⟩ from hs]
        exact hw
      · simp [List.map_cons, first, hm, hd]
      · simp [List.flatMap_cons, contractBlock, first, hnext, hb]
termination_by l.length

/-- One based traversal of an actual permutation cycle. -/
noncomputable def cycleBoundary (σ : Equiv.Perm D) (d : D) : List D :=
  List.ofFn (fun k : Fin (Function.minimalPeriod σ d) ↦ σ^[k.val] d)

theorem cycleBoundary_walk (σ : Equiv.Perm D) (d : D) :
    Walk σ d d (cycleBoundary σ d) := by
  have h := Walk.of_iterate σ (Function.minimalPeriod σ d) d
  simpa only [cycleBoundary, Function.iterate_minimalPeriod] using h

theorem cycleBoundary_nodup (σ : Equiv.Perm D) (d : D) : (cycleBoundary σ d).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt h)

theorem mem_cycleBoundary_self [Finite D] (σ : Equiv.Perm D) (d : D) :
    d ∈ cycleBoundary σ d := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts d)
  exact List.mem_ofFn.mpr ⟨⟨0, hp⟩, rfl⟩

/-- Distinct nonempty closed departures are the actual based cycle boundary. -/
theorem Walk.eq_cycleBoundary {σ : Equiv.Perm D} {d : D} {l : List D}
    (h : Walk σ d d l) (hn : l ≠ []) (hnd : l.Nodup) : l = cycleBoundary σ d := by
  have he := h.departures
  have hl := h.length_eq_minimalPeriod hn hnd
  simpa [cycleBoundary, hl] using he

/-- The complete based cyclic word is preserved by contraction and block concatenation. -/
theorem contract_cycle_word [Finite D] (σ : Equiv.Perm D) (a : D) (ha : σ a ≠ a)
    (block : D → List Y) (d : {d : D // d ≠ a}) :
    (cycleBoundary (contract σ a) d).flatMap (contractBlock σ a block) =
      (cycleBoundary σ d.val).flatMap block := by
  classical
  obtain ⟨out, hw, hm, hb⟩ := contract_walk σ a ha block (cycleBoundary_walk σ d.val)
    d.property d.property
  have hnd : out.Nodup := by
    apply List.Nodup.of_map (f := Subtype.val)
    rw [hm]
    exact (cycleBoundary_nodup σ d.val).filter _
  have hn : out ≠ [] := by
    intro hz
    have hd : d.val ∈ (cycleBoundary σ d.val).filter (fun x ↦ decide (x ≠ a)) :=
      List.mem_filter.mpr ⟨mem_cycleBoundary_self σ d.val, by simpa using d.property⟩
    rw [← hm, hz] at hd
    simp at hd
  rw [hw.eq_cycleBoundary hn hnd] at hb
  exact hb

/-- Relabelling darts by a conjugacy transports the entire ordered walk. -/
theorem Walk.map_equiv {E : Type*} {σ : Equiv.Perm D} {τ : Equiv.Perm E}
    (f : D ≃ E) (hf : ∀ d, f (σ d) = τ (f d)) {d e : D} {l : List D}
    (h : Walk σ d e l) : Walk τ (f d) (f e) (l.map f) := by
  induction h with
  | nil => exact .nil _
  | cons d e l _ ih =>
    apply Walk.cons
    simpa only [hf] using ih

/-- Conjugacy transports the full based cyclic order, not just its cycle class. -/
theorem cycleBoundary_map [Finite D] {E : Type*} (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (f : D ≃ E) (hf : ∀ d, f (σ d) = τ (f d)) (d : D) :
    (cycleBoundary σ d).map f = cycleBoundary τ (f d) := by
  have hw := (cycleBoundary_walk σ d).map_equiv f hf
  apply hw.eq_cycleBoundary
  · intro h
    have he : cycleBoundary σ d = [] := List.map_eq_nil_iff.mp h
    have hm := mem_cycleBoundary_self σ d
    rw [he] at hm
    exact List.not_mem_nil hm
  · exact (cycleBoundary_nodup σ d).map f.injective

end SmallPresentationStatements.PermutationCycles
