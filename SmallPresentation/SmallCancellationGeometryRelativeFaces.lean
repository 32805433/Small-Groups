module

public import SmallPresentation.SmallCancellationGeometryBigonFaces
public import SmallPresentation.SmallCancellationGeometryBigonWords

/-!
# Relative region equations under actual bigon suppression

The face-coordinate equivalence of bigon suppression preserves the entire ordered face
boundary, not merely its cycle class. Transporting arbitrary face weights by that map
therefore preserves their products and the distinguished outside face. For relative region
equations, the face weights are inverses of the vertex corner coefficients.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D E : Type*}

/-- An intertwining map carries the complete ordered departure list of a walk. -/
theorem Walk.map_intertwining {σ : Equiv.Perm D} {τ : Equiv.Perm E}
    (f : D → E) (hf : ∀ d, f (σ d) = τ (f d)) {d e : D} {l : List D}
    (h : Walk σ d e l) : Walk τ (f d) (f e) (l.map f) := by
  induction h with
  | nil => exact .nil _
  | cons d e l _ ih =>
    apply Walk.cons
    simpa only [hf] using ih

/-- An injective intertwining map preserves the full based cycle boundary. -/
theorem cycleBoundary_map_injective [Finite D] (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (f : D → E) (hinj : Function.Injective f)
    (hf : ∀ d, f (σ d) = τ (f d)) (d : D) :
    (cycleBoundary σ d).map f = cycleBoundary τ (f d) := by
  apply ((cycleBoundary_walk σ d).map_intertwining f hf).eq_cycleBoundary
  · intro he
    have hz := List.map_eq_nil_iff.mp he
    have hm := mem_cycleBoundary_self σ d
    rw [hz] at hm
    exact List.not_mem_nil hm
  · exact (cycleBoundary_nodup σ d).map hinj

end SmallPresentationStatements.PermutationCycles

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D H : Type*} [Group H] (P : RibbonMap D)

/-- A coefficient relation on a face of period at most two gives its two-corner equation,
including the degenerate period-one case. -/
theorem two_step_corner_equation (corner : D → H) (d e : D)
    (h₁ : P.face d = e) (h₂ : P.face e = d)
    (hface : ((P.faceBoundary d).map (fun x ↦ (corner x)⁻¹)).prod = 1) : corner d * corner e = 1 := by
  by_cases he : d = e
  · cases he
    have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr h₁
    have hc : corner d = 1 := by simpa [faceBoundary, hp] using hface
    simp [hc]
  · have hperiodic : Function.IsPeriodicPt P.face 2 d := by
      change P.face (P.face d) = d
      rw [h₁, h₂]
    have hle := hperiodic.minimalPeriod_le (by decide : 0 < 2)
    have hpos := hperiodic.minimalPeriod_pos (by decide : 0 < 2)
    have hne : Function.minimalPeriod P.face d ≠ 1 := by
      intro hp
      have hh := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hp
      exact he (hh.symm.trans h₁)
    have hp : Function.minimalPeriod P.face d = 2 := by omega
    have hh : (corner d)⁻¹ * (corner e)⁻¹ = 1 := by
      simpa [faceBoundary, hp, List.ofFn_succ, h₁] using hface
    exact mul_eq_one_comm.mp (by
      simpa only [mul_inv_rev, inv_inv, inv_one] using congrArg Inv.inv hh)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D H : Type*} {P : RibbonMap D} (B : Bigon P)

/-- The old corner represented by each surviving face dart. -/
noncomputable def faceCoordinate (d : B.Dart) : D := B.exchange d.val

theorem faceCoordinate_injective : Function.Injective B.faceCoordinate :=
  B.exchange.injective.comp Subtype.val_injective

theorem faceCoordinate_step (d : B.Dart) :
    B.faceCoordinate (B.suppress.face d) = P.face (B.faceCoordinate d) :=
  congrArg Subtype.val (B.face_conjugacy d)

/-- Suppression preserves the exact ordered boundary of each surviving face. -/
theorem faceBoundary_map [Finite D] (d : B.Dart) :
    (B.suppress.faceBoundary d).map B.faceCoordinate = P.faceBoundary (B.faceCoordinate d) := by
  simpa only [RibbonMap.faceBoundary, PermutationCycles.cycleBoundary, Equiv.Perm.coe_pow]
    using PermutationCycles.cycleBoundary_map_injective B.suppress.face P.face
      B.faceCoordinate B.faceCoordinate_injective B.faceCoordinate_step d

/-- Actual same-face membership is reflected as well as preserved. -/
theorem face_sameCycle_iff [Finite D] (d e : B.Dart) :
    B.suppress.face.SameCycle d e ↔ P.face.SameCycle (B.faceCoordinate d) (B.faceCoordinate e) := by
  rw [← B.suppress.mem_faceBoundary_iff, ← P.mem_faceBoundary_iff,
    ← B.faceBoundary_map]
  exact (List.mem_map_of_injective B.faceCoordinate_injective).symm

/-- Transported corner coefficients are the old corners at the actual face coordinates. -/
noncomputable def corners (corner : D → H) (d : B.Dart) : H := corner (B.faceCoordinate d)

/-- Every surviving face has exactly its former ordered product of arbitrary face weights. -/
theorem face_product [Finite D] [Monoid H] (corner : D → H) (d : B.Dart) :
    ((B.suppress.faceBoundary d).map (B.corners corner)).prod =
      ((P.faceBoundary (B.faceCoordinate d)).map corner).prod := by
  rw [← B.faceBoundary_map, List.map_map]
  rfl

/-- A chosen old outside dart outside the removed bigon gives an actual new outside dart. -/
noncomputable def outside (d : B.FaceDart) : B.Dart := B.faceDartEquiv.symm d

@[simp] theorem faceCoordinate_outside (d : B.FaceDart) : B.faceCoordinate (B.outside d) = d.val :=
  congrArg Subtype.val (B.faceDartEquiv.apply_symm_apply d)

/-- The distinguished outside dart survives in face coordinates when the suppressed bigon
is inner. This also covers outside darts at the opposite ends of the bigon's edges. -/
def outsideFaceDart (o : D) (hi : ¬ P.face.SameCycle o B.left) : B.FaceDart := by
  refine ⟨o, ?_, ?_⟩
  · intro he
    apply hi
    rw [he]
  · intro he
    apply hi
    rw [he, ← B.face_left]
    exact Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _)

/-- All inner-face weight equations survive actual bigon surgery. Apply this with inverse
corner weights for relative region equations. -/
theorem inner_equations [Finite D] [Monoid H] (corner : D → H) (o : B.FaceDart)
    (h : ∀ d, ¬ P.face.SameCycle o.val d → ((P.faceBoundary d).map corner).prod = 1)
    (d : B.Dart) (hi : ¬ B.suppress.face.SameCycle (B.outside o) d) :
    ((B.suppress.faceBoundary d).map (B.corners corner)).prod = 1 := by
  rw [B.face_product]
  apply h
  intro hh
  apply hi
  apply (B.face_sameCycle_iff _ _).mpr
  simpa only [B.faceCoordinate_outside] using hh

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
