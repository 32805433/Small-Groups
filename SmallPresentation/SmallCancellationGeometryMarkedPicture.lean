module

public import SmallPresentation.SmallCancellationGeometryMarkedRealization
public import SmallPresentation.SmallCancellationGeometryMarkedCurvature
public import SmallPresentation.SmallCancellationDipoleRelativeFactorFaces

/-!
# Marked relative pictures and their actual attaching vertices

The distinguished factor vertex carries an arbitrary nontrivial coefficient. All other
vertices are either factor relations or literal indexed attaching words. The attaching
count is the cardinality of the actual vertex quotient, not a chosen word expression.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D H : Type*} [Fintype D] [Group H] (P : RibbonMap D)

/-- The radial boundary theorem also recovers a sole omitted vertex equation from all
region equations and the other vertex equations. The coefficients need not commute. -/
theorem marked_corner_product_one (corner : D → H) (hc : P.Connected)
    (hE : P.EulerEquality) (marked : D)
    (hvertex : ∀ d, ¬P.rotation.SameCycle marked d →
      ((P.vertexBoundary d).map corner).prod = 1)
    (hfaces : ∀ d, ((P.faceBoundary d).map (fun e ↦ (corner e)⁻¹)).prod = 1) :
    ((P.vertexBoundary marked).map corner).prod = 1 := by
  have h := boundary_product_one (D × Bool) P.radial (radialWeight corner)
    (P.radialWeight_edge corner) (P.radial_connected hc) (P.radial_euler_iff.mpr hE)
    (marked, false) ?_
  · rw [P.radial_vertex_product_false] at h
    exact h
  · rintro ⟨d, b⟩ hd
    cases b
    · rw [P.radial_vertex_product_false]
      apply hvertex d
      intro hv
      exact hd (sameCycle_map_of_step P.rotation P.radial.rotation (fun e ↦ (e, false))
        (fun _ ↦ Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)) hv)
    · rw [P.radial_vertex_product_true]
      exact hfaces d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    {D : Type*} [Fintype D]

/-- Exact indexed readings only at genuine attaching vertices of a marked mixed picture. -/
structure MarkedMixedReadings {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)} (S : OldDiscSystem L) (marked : D) where
  origin : {d // ¬S.old d ∧ ¬P.rotation.SameCycle marked d} → Origin length
  forward : ∀ (d : D) (hd : ¬S.old d ∧ ¬P.rotation.SameCycle marked d),
    (L.arc d).2 = true → L.vertexWord d = Augmentation.word G length rows (origin ⟨d, hd⟩)
  backward : ∀ (d : D) (hd : ¬S.old d ∧ ¬P.rotation.SameCycle marked d),
    (L.arc d).2 = false →
      L.reverseVertexWord d = Augmentation.word G length rows (origin ⟨d, hd⟩)

/-- A finite marked counterexample picture. Its existence is a separate obligation,
constructed from an actual null factor element; no quotient injectivity is assumed. -/
structure MarkedRelativePicture (D : Type) [Fintype D] where
  map : RibbonMap D
  labels : RibbonLabelling map A (Monoid.CoprodI G)
  marked : D
  marked_size : (map.vertexBoundary marked).length = 2
  oldDiscs : OldDiscSystem labels
  marked_not_old : ¬oldDiscs.old marked
  shape : FactorVertexShape labels marked
  nontrivial : ((map.vertexBoundary marked).map labels.corner).prod ≠ 1
  readings : MarkedMixedReadings G length rows oldDiscs marked
  factorCorners : RibbonLabelling.FactorCorners G labels
  connected : map.Connected
  euler : map.EulerEquality
  faces : ∀ d, labels.faceValue d = 1

namespace MarkedRelativePicture

variable {G length rows} {D : Type} [Fintype D]
    (T : MarkedRelativePicture G length rows D)

/-- An actual attaching incidence is neither a factor relation nor the marked boundary. -/
def IsNew (d : D) : Prop := ¬T.oldDiscs.old d ∧ ¬T.map.rotation.SameCycle T.marked d

theorem isNew_sameCycle {d e : D} (h : T.map.rotation.SameCycle d e) :
    T.IsNew d ↔ T.IsNew e := by
  constructor
  · rintro ⟨ho, hm⟩
    exact ⟨fun he ↦ ho ((T.oldDiscs.constant h).mpr he), fun he ↦ hm (he.trans h.symm)⟩
  · rintro ⟨ho, hm⟩
    exact ⟨fun hd ↦ ho ((T.oldDiscs.constant h).mp hd), fun hd ↦ hm (hd.trans h)⟩

/-- The subtype of the actual ribbon vertex quotient occupied by attaching rows. -/
def NewVertex := {v : T.map.Vertex // ∃ d, T.map.vertexOf d = v ∧ T.IsNew d}

noncomputable instance : Fintype T.NewVertex := by
  classical
  unfold NewVertex
  exact Fintype.ofFinite _

noncomputable def newCount : ℕ := Fintype.card T.NewVertex

/-- An old-only marked picture contradicts the noncommutative planar boundary theorem. -/
theorem exists_new : ∃ d, T.IsNew d := by
  by_contra hn
  apply T.nontrivial
  apply T.map.marked_corner_product_one T.labels.corner T.connected T.euler T.marked
  · intro d hd
    have ho : T.oldDiscs.old d := by
      by_contra ho
      exact hn ⟨d, ho, hd⟩
    exact (T.oldDiscs.disc d ho).product
  · exact T.faces

/-- Every counterexample has a positive attaching-disc count. -/
theorem newCount_pos : 0 < T.newCount := by
  obtain ⟨d, hd⟩ := T.exists_new
  have : Nonempty T.NewVertex := ⟨⟨T.map.vertexOf d, d, rfl, hd⟩⟩
  exact Fintype.card_pos

end MarkedRelativePicture
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
