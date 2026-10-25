module

public import SmallPresentation.SmallCancellationGeometryRelativeOriginalBands
public import SmallPresentation.SmallCancellationBandPieces

/-!
# Metric bounds on compressed relative bands

Original incidence blocks, their exact reversed matching, and preserved internal corner
equations turn positive augmented arcs into actual semi-initial pieces.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace AlternatingBlock

variable {Y : Type*} (sign : Y → Bool)

/-- Count positive incidences in a nonempty alternating block. -/
theorem count_positive (x : Y) (l : List Y)
    (h : (x :: l).IsChain (fun y z ↦ sign z = !(sign y))) :
    (x :: l).countP sign = ((x :: l).length + if sign x then 1 else 0) / 2 := by
  induction l generalizing x with
  | nil => cases hx : sign x <;> simp [hx]
  | cons y l ih =>
    have hh := List.isChain_cons_cons.mp h
    have ht := ih y hh.2
    simp only [List.countP_cons, List.length_cons] at ht ⊢
    have hxy := hh.1
    cases hx : sign x <;> cases hy : sign y <;> simp_all
    all_goals omega

end AlternatingBlock

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]
variable (rows : ∀ i, Fin (length i) → Syllable G)
variable {Y : Type*} (P : RibbonMap Y)
variable (L : RibbonLabelling P A (Monoid.CoprodI G))

/-- Exact indexed row readings in both orientations of an augmented ribbon. These are
word-reading data; metric bounds and degrees are consequences proved below. -/
structure AugmentedReadings where
  origin : Y → Origin length
  forward : ∀ y, (L.arc y).2 = true →
    L.vertexWord y = Augmentation.word G length rows (origin y)
  backward : ∀ y, (L.arc y).2 = false →
    L.reverseVertexWord y = Augmentation.word G length rows (origin y)

namespace AugmentedReadings

variable (Q : AugmentedReadings G length rows P L)

variable {G length rows P L}

theorem period (y : Y) : Function.minimalPeriod P.rotation y =
    2 * length (Q.origin y).row := by
  cases hs : (L.arc y).2 with
  | false => simpa using congrArg List.length (Q.backward y hs)
  | true => simpa [RibbonLabelling.vertexWord] using congrArg List.length (Q.forward y hs)

/-- The alternating marker signs follow from the actual complete row readings. -/
theorem alternating (Q : AugmentedReadings G length rows P L) (y : Y) : (L.arc (P.rotation y)).2 = !((L.arc y).2) := by
  have hpos (z : Y) : 0 < length (Q.origin z).row := Fin.pos (Q.origin z).position
  cases hs : (L.arc y).2 with
  | true =>
    have hh := OppositeBand.forward_reading G length rows L y (Q.origin y)
      (Q.forward y hs) 1 (by have := hpos y; omega)
    have hsign := congrArg (fun p ↦ p.1.2) hh
    simpa [Augmentation.entry, hs] using hsign
  | false =>
    cases ht : (L.arc (P.rotation y)).2 with
    | true => rfl
    | false =>
      have hh := OppositeBand.reverse_reading G length rows L (P.rotation y)
        (Q.origin (P.rotation y)) (Q.backward (P.rotation y) ht) 1
        (by have := hpos (P.rotation y); omega)
      have hsign := congrArg (fun p ↦ p.1.2) hh
      simp [Augmentation.entry, reverseLetter, hs] at hsign

theorem rowLength_iterate [Finite Y] (y : Y) (k : ℕ) :
    length (Q.origin (P.rotation^[k] y)).row = length (Q.origin y).row := by
  have hh := Function.minimalPeriod_apply_iterate (P.rotation.injective.mem_periodicPts y) k
  rw [Q.period, Q.period] at hh
  omega

theorem boundary_alternating (Q : AugmentedReadings G length rows P L) (y : Y) :
    (P.vertexBoundary y).IsChain (fun z w ↦ (L.arc w).2 = !((L.arc z).2)) := by
  rw [List.isChain_iff_getElem]
  intro k hk
  simpa [RibbonMap.vertexBoundary, Equiv.Perm.coe_pow, Function.iterate_succ_apply'] using
    Q.alternating (P.rotation^[k] y)

/-- Each augmented original vertex contains exactly one positive incidence per syllable. -/
theorem boundary_count_positive [Finite Y] (y : Y) :
    (P.vertexBoundary y).countP (fun z ↦ (L.arc z).2) = length (Q.origin y).row := by
  obtain ⟨tail, he⟩ := P.vertexBoundary_eq_cons y
  have hc := AlternatingBlock.count_positive (fun z ↦ (L.arc z).2) y tail
    (by rw [← he]; exact Q.boundary_alternating y)
  rw [← he] at hc
  simp only [RibbonMap.vertexBoundary_length, Q.period] at hc
  cases hs : (L.arc y).2 <;> simp [hs] at hc <;> omega

theorem rowLength_of_mem_boundary [Finite Y] (y z : Y) (hz : z ∈ P.vertexBoundary y) :
    length (Q.origin z).row = length (Q.origin y).row := by
  have hh : z ∈ List.ofFn (fun k : Fin (Function.minimalPeriod P.rotation y) ↦
      P.rotation^[k.val] y) := by
    simpa [RibbonMap.vertexBoundary, Equiv.Perm.coe_pow] using hz
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hh
  rw [← hk]
  exact Q.rowLength_iterate y k.val

section Recorded

variable {D : Type*} [Finite D] [Finite Y]
variable (R : TaggedRelativeBlockRibbon (D := D) Y A (Monoid.CoprodI G) Y
  (fun y ↦ (L.arc y, L.corner y)) P.vertexBoundary P.edge)

omit [Finite Y] in
theorem block_alternating (Q : AugmentedReadings G length rows P L) (d : D) :
    (R.block d).IsChain (fun y z ↦ (L.arc z).2 = !((L.arc y).2)) := by
  rw [List.isChain_iff_getElem]
  intro k hk
  rw [R.block_getElem P d k (by omega), R.block_getElem P d (k + 1) hk]
  simpa [Function.iterate_succ_apply'] using Q.alternating (P.rotation^[k] (R.relator d))

omit [Finite Y] in
theorem block_eq_cons (d : D) : ∃ tail, R.block d = R.relator d :: tail := by
  cases he : R.block d with
  | nil => exact False.elim (R.block_nonempty d he)
  | cons x tail =>
    have hh := R.block_getElem P d 0 (by rw [he]; simp)
    simp only [he, List.getElem_cons_zero, Function.iterate_zero_apply] at hh
    exact ⟨tail, by simp [hh]⟩

omit [Finite Y] in
theorem block_count_positive (Q : AugmentedReadings G length rows P L) (d : D) :
    (R.block d).countP (fun y ↦ (L.arc y).2) =
      ((R.block d).length + if (L.arc (R.relator d)).2 then 1 else 0) / 2 := by
  obtain ⟨tail, he⟩ := block_eq_cons R d
  have hh := AlternatingBlock.count_positive (fun y ↦ (L.arc y).2) (R.relator d) tail
    (by rw [← he]; exact Q.block_alternating R d)
  simpa only [← he] using hh

/-- A compressed edge's positive original incidences satisfy the metric bound. The proof
trims at most one negative marker at each end and constructs an actual semi-initial piece
from the original matched band and its preserved internal coefficient equations. -/
theorem block_metric_bound
    (hmetric : MetricSmallCancellation G length rows)
    (hnodipole : ∀ y, (L.arc y).2 = true → Q.origin (P.edge y) ≠ Q.origin y)
    (d : D) :
    6 * (R.block d).countP (fun y ↦ (L.arc y).2) < length (Q.origin (R.relator d)).row := by
  let m := (R.block d).countP (fun y ↦ (L.arc y).2)
  have hmdef : m = ((R.block d).length + if (L.arc (R.relator d)).2 then 1 else 0) / 2 :=
    Q.block_count_positive R d
  by_cases hm : m = 0
  · change 6 * m < _
    rw [hm]
    simpa using Fin.pos (Q.origin (R.relator d)).position
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let start : ℕ := if (L.arc (R.relator d)).2 then 0 else 1
  have hsize : start + (2 * m - 1) ≤ (R.block d).length := by
    dsimp [start]
    cases hs : (L.arc (R.relator d)).2 <;> simp [hs] at hmdef ⊢ <;> omega
  let B := (R.originalBand P d).subinterval start (2 * m - 1) hsize
  have hup : (L.arc (B.upper 0)).2 = true := by
    change (L.arc (P.rotation^[start + 0] (R.relator d))).2 = true
    dsimp [start]
    cases hs : (L.arc (R.relator d)).2 with
    | true => simp [hs]
    | false => simpa [hs] using Q.alternating (R.relator d)
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
    exact hnodipole _ hup
  have hp := B.piece_of_augmented_cornerEquations G length rows L
    (Q.origin (B.upper 0)) (Q.origin (B.lower 0)) hmpos hne
    (Q.forward _ hup) (Q.backward _ hlo) hc
  have hb := hmetric _ m hp
  have hlen : length (Q.origin (B.upper 0)).row = length (Q.origin (R.relator d)).row := by
    exact Q.rowLength_iterate (R.relator d) (start + 0)
  rwa [hlen] at hb

omit [Finite Y] in
/-- A surviving incidence on a compressed vertex still points to the same original vertex. -/
theorem relator_mem_original_boundary (d e : D) (he : e ∈ R.map.vertexBoundary d) :
    R.relator e ∈ P.vertexBoundary (R.relator d) := by
  rw [← R.relator_word d]
  apply List.mem_flatMap.mpr
  refine ⟨e, he, ?_⟩
  obtain ⟨tail, ht⟩ := block_eq_cons R e
  simp [ht]

omit [Finite D] in
/-- Counting positive original incidences through the exact vertex partition recovers the
whole indexed row length. -/
theorem vertex_count_positive (d : D) :
    ((R.map.vertexBoundary d).map
      (fun e ↦ (R.block e).countP (fun y ↦ (L.arc y).2))).sum =
      length (Q.origin (R.relator d)).row := by
  have hh := Q.boundary_count_positive (R.relator d)
  rw [← R.relator_word d, List.countP_flatMap] at hh
  exact hh

/-- Metric small cancellation forces at least seven surviving blocks around every vertex.
All pieces are extracted from actual opposite original incidence bands. -/
theorem seven_le_vertex_length
    (hmetric : MetricSmallCancellation G length rows)
    (hnodipole : ∀ y, (L.arc y).2 = true → Q.origin (P.edge y) ≠ Q.origin y)
    (d : D) : 7 ≤ (R.map.vertexBoundary d).length := by
  let ℓ := length (Q.origin (R.relator d)).row
  let ms := (R.map.vertexBoundary d).map (fun e ↦ (R.block e).countP (fun y ↦ (L.arc y).2))
  have hsum : ms.sum = ℓ := Q.vertex_count_positive R d
  have hpos : 0 < ℓ := Fin.pos (Q.origin (R.relator d)).position
  have hbound : ∀ m ∈ ms, 6 * m ≤ ℓ - 1 := by
    intro m hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    have hb := Q.block_metric_bound R hmetric hnodipole e
    have heq := Q.rowLength_of_mem_boundary (R.relator d) (R.relator e)
      (relator_mem_original_boundary R d e he)
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

end AugmentedReadings

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
