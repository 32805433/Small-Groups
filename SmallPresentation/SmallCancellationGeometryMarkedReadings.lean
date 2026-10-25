module

public import SmallPresentation.SmallCancellationGeometryMarkedReduction

/-! Exact augmented row readings away from one marked factor boundary. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    {Y : Type*} (P : RibbonMap Y) (L : RibbonLabelling P A (Monoid.CoprodI G)) (marked : Y)

/-- The marked vertex is not assigned a fictitious relator reading. All other vertices
retain their full exact row words in both orientations. -/
structure AugmentedReadingsExcept where
  origin : Y → Origin length
  forward : ∀ y, ¬P.rotation.SameCycle marked y → (L.arc y).2 = true →
    L.vertexWord y = Augmentation.word G length rows (origin y)
  backward : ∀ y, ¬P.rotation.SameCycle marked y → (L.arc y).2 = false →
    L.reverseVertexWord y = Augmentation.word G length rows (origin y)

namespace AugmentedReadingsExcept

variable {G length rows P L marked}
    (Q : AugmentedReadingsExcept G length rows P L marked)

/-- Being outside the marked vertex is stable under its actual rotation. -/
theorem regular_iterate (y : Y) (hy : ¬P.rotation.SameCycle marked y) (k : ℕ) :
    ¬P.rotation.SameCycle marked (P.rotation^[k] y) := by
  intro h
  exact hy (h.trans (Equiv.Perm.sameCycle_pow_right.mpr (.refl P.rotation y)).symm)

include Q in
theorem period (y : Y) (hy : ¬P.rotation.SameCycle marked y) :
    Function.minimalPeriod P.rotation y = 2 * length (Q.origin y).row := by
  cases hs : (L.arc y).2 with
  | false => simpa using congrArg List.length (Q.backward y hy hs)
  | true => simpa [RibbonLabelling.vertexWord] using congrArg List.length (Q.forward y hy hs)

include Q in
theorem alternating (y : Y) (hy : ¬P.rotation.SameCycle marked y) :
    (L.arc (P.rotation y)).2 = !((L.arc y).2) := by
  have hpos (z : Y) : 0 < length (Q.origin z).row := Fin.pos (Q.origin z).position
  cases hs : (L.arc y).2 with
  | true =>
    have hh := OppositeBand.forward_reading G length rows L y (Q.origin y)
      (Q.forward y hy hs) 1 (by have := hpos y; omega)
    simpa [Augmentation.entry, hs] using congrArg (fun p ↦ p.1.2) hh
  | false =>
    cases ht : (L.arc (P.rotation y)).2 with
    | true => rfl
    | false =>
      have hyr : ¬P.rotation.SameCycle marked (P.rotation y) := regular_iterate y hy 1
      have hh := OppositeBand.reverse_reading G length rows L (P.rotation y)
        (Q.origin (P.rotation y)) (Q.backward (P.rotation y) hyr ht) 1
        (by have := hpos (P.rotation y); omega)
      have hsign := congrArg (fun p ↦ p.1.2) hh
      simp [Augmentation.entry, reverseLetter, hs] at hsign

theorem rowLength_iterate [Finite Y] (y : Y) (hy : ¬P.rotation.SameCycle marked y) (k : ℕ) :
    length (Q.origin (P.rotation^[k] y)).row = length (Q.origin y).row := by
  have hh := Function.minimalPeriod_apply_iterate (P.rotation.injective.mem_periodicPts y) k
  rw [Q.period _ (regular_iterate y hy k), Q.period y hy] at hh
  omega

include Q in
theorem boundary_alternating (y : Y) (hy : ¬P.rotation.SameCycle marked y) :
    (P.vertexBoundary y).IsChain (fun z w ↦ (L.arc w).2 = !((L.arc z).2)) := by
  rw [List.isChain_iff_getElem]
  intro k hk
  simpa [RibbonMap.vertexBoundary, Equiv.Perm.coe_pow, Function.iterate_succ_apply'] using
    Q.alternating (P.rotation^[k] y) (regular_iterate y hy k)

theorem boundary_count_positive [Finite Y] (y : Y) (hy : ¬P.rotation.SameCycle marked y) :
    (P.vertexBoundary y).countP (fun z ↦ (L.arc z).2) = length (Q.origin y).row := by
  obtain ⟨tail, he⟩ := P.vertexBoundary_eq_cons y
  have hc := AlternatingBlock.count_positive (fun z ↦ (L.arc z).2) y tail
    (by rw [← he]; exact Q.boundary_alternating y hy)
  rw [← he] at hc
  simp only [RibbonMap.vertexBoundary_length, Q.period y hy] at hc
  cases hs : (L.arc y).2 <;> simp [hs] at hc <;> omega

theorem regular_of_mem_boundary [Finite Y] (y z : Y) (hy : ¬P.rotation.SameCycle marked y)
    (hz : z ∈ P.vertexBoundary y) : ¬P.rotation.SameCycle marked z := by
  intro h
  exact hy (h.trans ((P.mem_vertexBoundary_iff y z).mp hz).symm)

theorem rowLength_of_mem_boundary [Finite Y] (y z : Y)
    (hy : ¬P.rotation.SameCycle marked y) (hz : z ∈ P.vertexBoundary y) :
    length (Q.origin z).row = length (Q.origin y).row := by
  have hh : z ∈ List.ofFn (fun k : Fin (Function.minimalPeriod P.rotation y) ↦
      P.rotation^[k.val] y) := by
    simpa [RibbonMap.vertexBoundary, Equiv.Perm.coe_pow] using hz
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hh
  rw [← hk]
  exact Q.rowLength_iterate y hy k.val

section Recorded

variable {D : Type*} [Finite D] [Finite Y]
    (R : TaggedRelativeBlockRibbon (D := D) Y A (Monoid.CoprodI G) Y
      (fun y ↦ (L.arc y, L.corner y)) P.vertexBoundary P.edge)

include Q in
omit [Finite Y] in
theorem block_alternating (d : D) (hd : ¬P.rotation.SameCycle marked (R.relator d)) :
    (R.block d).IsChain (fun y z ↦ (L.arc z).2 = !((L.arc y).2)) := by
  rw [List.isChain_iff_getElem]
  intro k hk
  rw [R.block_getElem P d k (by omega), R.block_getElem P d (k + 1) hk]
  simpa [Function.iterate_succ_apply'] using
    Q.alternating (P.rotation^[k] (R.relator d)) (regular_iterate _ hd k)

include Q in
omit [Finite Y] in
theorem block_count_positive (d : D) (hd : ¬P.rotation.SameCycle marked (R.relator d)) :
    (R.block d).countP (fun y ↦ (L.arc y).2) =
      ((R.block d).length + if (L.arc (R.relator d)).2 then 1 else 0) / 2 := by
  obtain ⟨tail, he⟩ := AugmentedReadings.block_eq_cons R d
  have hh := AlternatingBlock.count_positive (fun y ↦ (L.arc y).2) (R.relator d) tail
    (by rw [← he]; exact Q.block_alternating R d hd)
  simpa only [← he] using hh

/-- Bands opposite the marked vertex are bounded by its actual two incidences; bands
opposite another relator are genuine metric pieces. -/
theorem block_metric_bound
    (hmetric : MetricSmallCancellation G length rows)
    (hsmall : (P.vertexBoundary marked).length ≤ 2)
    (hnodipole : ∀ y, ¬P.rotation.SameCycle marked y → (L.arc y).2 = true →
      ¬P.rotation.SameCycle marked (P.edge y) → Q.origin (P.edge y) ≠ Q.origin y)
    (d : D) (hd : ¬P.rotation.SameCycle marked (R.relator d)) :
    6 * (R.block d).countP (fun y ↦ (L.arc y).2) < length (Q.origin (R.relator d)).row := by
  by_cases hop : P.rotation.SameCycle marked (R.relator (R.map.edge d))
  · apply R.block_metric_bound_of_short_opposite P (fun y ↦ (L.arc y).2) d
    · exact (P.vertexBoundary_length_eq_of_sameCycle hop).symm.le.trans hsmall
    · exact Q.block_alternating R d hd
    · exact seven_le_length_of_metric G length rows hmetric _
  let m := (R.block d).countP (fun y ↦ (L.arc y).2)
  have hmdef : m = ((R.block d).length + if (L.arc (R.relator d)).2 then 1 else 0) / 2 :=
    Q.block_count_positive R d hd
  by_cases hm : m = 0
  · change 6 * m < _
    rw [hm]
    exact Fin.pos (Q.origin (R.relator d)).position
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let start : ℕ := if (L.arc (R.relator d)).2 then 0 else 1
  have hsize : start + (2 * m - 1) ≤ (R.block d).length := by
    dsimp [start]
    cases hs : (L.arc (R.relator d)).2 <;> simp [hs] at hmdef ⊢ <;> omega
  let B := (R.originalBand P d).subinterval start (2 * m - 1) hsize
  have hupper : ¬P.rotation.SameCycle marked (B.upper 0) := regular_iterate _ hd (start + 0)
  have hlower : ¬P.rotation.SameCycle marked (B.lower 0) := by
    change ¬P.rotation.SameCycle marked (P.edge (P.rotation^[start + 0] (R.relator d)))
    rw [R.lower_as_iterate P d (start + 0) (by omega)]
    exact regular_iterate _ hop _
  have hup : (L.arc (B.upper 0)).2 = true := by
    change (L.arc (P.rotation^[start + 0] (R.relator d))).2 = true
    dsimp [start]
    cases hs : (L.arc (R.relator d)).2 with
    | true => simp [hs]
    | false => simpa [hs] using Q.alternating (R.relator d) hd
  have hlo : (L.arc (B.lower 0)).2 = false := by
    have hh := L.edge_arc (B.upper 0)
    rw [B.edge_match 0 (by omega)] at hh
    simpa [reverseLetter, hup] using congrArg Prod.snd hh
  have hc (k : ℕ) (hk : k + 1 < 2 * m - 1) :
      L.corner (B.upper k) * L.corner (B.lower (k + 1)) = 1 := by
    simpa only [B, OppositeBand.subinterval, Nat.add_assoc] using
      R.originalBand_corner_equations P d (start + k) (by omega)
  have hne : Q.origin (B.lower 0) ≠ Q.origin (B.upper 0) := by
    rw [← B.edge_match 0 (by omega)]
    exact hnodipole _ hupper hup (by simpa only [B.edge_match 0 (by omega)] using hlower)
  have hp := B.piece_of_augmented_cornerEquations G length rows L
    (Q.origin (B.upper 0)) (Q.origin (B.lower 0)) hmpos hne
    (Q.forward _ hupper hup) (Q.backward _ hlower hlo) hc
  have hb := hmetric _ m hp
  have hlen : length (Q.origin (B.upper 0)).row = length (Q.origin (R.relator d)).row :=
    Q.rowLength_iterate _ hd (start + 0)
  rwa [hlen] at hb

omit [Finite D] in
theorem vertex_count_positive (d : D) (hd : ¬P.rotation.SameCycle marked (R.relator d)) :
    ((R.map.vertexBoundary d).map
      (fun e ↦ (R.block e).countP (fun y ↦ (L.arc y).2))).sum =
      length (Q.origin (R.relator d)).row := by
  have hh := Q.boundary_count_positive (R.relator d) hd
  rw [← R.relator_word d, List.countP_flatMap] at hh
  exact hh

/-- Every nonboundary relator vertex retains at least seven compressed bands. -/
theorem seven_le_vertex_length
    (hmetric : MetricSmallCancellation G length rows)
    (hsmall : (P.vertexBoundary marked).length ≤ 2)
    (hnodipole : ∀ y, ¬P.rotation.SameCycle marked y → (L.arc y).2 = true →
      ¬P.rotation.SameCycle marked (P.edge y) → Q.origin (P.edge y) ≠ Q.origin y)
    (d : D) (hd : ¬P.rotation.SameCycle marked (R.relator d)) :
    7 ≤ (R.map.vertexBoundary d).length := by
  let ℓ := length (Q.origin (R.relator d)).row
  let ms := (R.map.vertexBoundary d).map (fun e ↦ (R.block e).countP (fun y ↦ (L.arc y).2))
  have hsum : ms.sum = ℓ := Q.vertex_count_positive R d hd
  have hpos : 0 < ℓ := Fin.pos (Q.origin (R.relator d)).position
  have hbound : ∀ m ∈ ms, 6 * m ≤ ℓ - 1 := by
    intro m hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    have hmem := AugmentedReadings.relator_mem_original_boundary R d e he
    have hb := Q.block_metric_bound R hmetric hsmall hnodipole e
      (regular_of_mem_boundary _ _ hd hmem)
    have heq := Q.rowLength_of_mem_boundary (R.relator d) (R.relator e) hd hmem
    change length (Q.origin (R.relator e)).row = ℓ at heq
    rw [heq] at hb
    omega
  have sumBound (ns : List ℕ) : (∀ m ∈ ns, 6 * m ≤ ℓ - 1) →
      6 * ns.sum ≤ (ℓ - 1) * ns.length := by
    induction ns with
    | nil => simp
    | cons m tail ih =>
      intro hns
      have hm := hns m (by simp)
      have ht := ih (fun n hn ↦ hns n (by simp [hn]))
      simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_succ]
      omega
  have hb := sumBound ms hbound
  have hlen : ms.length = (R.map.vertexBoundary d).length := by simp [ms]
  by_contra hn
  have hn' : ms.length ≤ 6 := by omega
  have hh := Nat.mul_le_mul_left (ℓ - 1) hn'
  rw [hsum] at hb
  omega

end Recorded
end AugmentedReadingsExcept
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
