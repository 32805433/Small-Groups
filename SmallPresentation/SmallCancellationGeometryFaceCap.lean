module

public import SmallPresentation.SmallCancellationGeometryCornerCancellationComponents
public import SmallPresentation.SmallCancellationDipoleRelativeFactorFaces

/-! A concrete two-marker factor vertex inserted across an existing edge. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap

open PermutationCycles

variable {D : Type*} (P : RibbonMap D) (a : D)

noncomputable def switch : Equiv.Perm (D ⊕ Bool) := by
  classical
  exact Equiv.swap (.inl (P.edge a)) (.inr true)

def oldEdge : Equiv.Perm (D ⊕ Bool) := Equiv.sumCongr P.edge (Equiv.swap false true)

theorem oldEdge_involutive : Function.Involutive (oldEdge P) := by
  rintro (d | b)
  · exact congrArg Sum.inl (P.edge_involutive d)
  · cases b <;> rfl

theorem oldEdge_ne (d : D ⊕ Bool) : oldEdge P d ≠ d := by
  rcases d with d | b
  · exact fun h ↦ P.edge_ne d (Sum.inl.inj h)
  · cases b <;> simp [oldEdge, Equiv.sumCongr_apply]

noncomputable def map : RibbonMap (D ⊕ Bool) where
  edge := (switch P a).trans ((oldEdge P).trans (switch P a))
  edge_involutive d := by
    classical
    change switch P a (oldEdge P (switch P a (switch P a (oldEdge P (switch P a d))))) = d
    simp only [switch, Equiv.swap_apply_self]
    rw [oldEdge_involutive, Equiv.swap_apply_self]
  edge_ne d := by
    intro h
    apply oldEdge_ne P (switch P a d)
    have hh := congrArg (switch P a) h
    simpa only [Equiv.trans_apply, switch, Equiv.swap_apply_self] using hh
  rotation := Equiv.sumCongr P.rotation (Equiv.swap false true)

@[simp] theorem rotation_old (d : D) : (map P a).rotation (.inl d) = .inl (P.rotation d) := rfl
@[simp] theorem rotation_positive : (map P a).rotation (.inr false) = .inr true := rfl
@[simp] theorem rotation_negative : (map P a).rotation (.inr true) = .inr false := rfl

@[simp] theorem edge_positive : (map P a).edge (.inr false) = .inl (P.edge a) := by
  classical
  change switch P a (oldEdge P (switch P a (.inr false))) = _
  have hs : switch P a (.inr false) = .inr false :=
    Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
  rw [hs]
  change switch P a (.inr true) = _
  exact Equiv.swap_apply_right _ _

@[simp] theorem edge_negative : (map P a).edge (.inr true) = .inl a := by
  classical
  change switch P a (oldEdge P (switch P a (.inr true))) = _
  rw [show switch P a (.inr true) = .inl (P.edge a) from Equiv.swap_apply_right _ _]
  change switch P a (.inl (P.edge (P.edge a))) = _
  rw [P.edge_involutive a]
  exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ P.edge_ne a (Sum.inl.inj h).symm) (by simp)

@[simp] theorem edge_anchor : (map P a).edge (.inl a) = .inr true := by
  have hh := (map P a).edge_involutive (.inr true)
  rwa [edge_negative] at hh

@[simp] theorem edge_mate : (map P a).edge (.inl (P.edge a)) = .inr false := by
  have hh := (map P a).edge_involutive (.inr false)
  rwa [edge_positive] at hh

theorem edge_old (d : D) (ha : d ≠ a) (he : d ≠ P.edge a) :
    (map P a).edge (.inl d) = .inl (P.edge d) := by
  classical
  change switch P a (oldEdge P (switch P a (.inl d))) = _
  have hde : (Sum.inl d : D ⊕ Bool) ≠ .inl (P.edge a) := fun h ↦ he (Sum.inl.inj h)
  have hmate : (Sum.inl (P.edge d) : D ⊕ Bool) ≠ .inl (P.edge a) :=
    fun h ↦ ha (P.edge.injective (Sum.inl.inj h))
  simp only [switch, Equiv.swap_apply_of_ne_of_ne hde (show (Sum.inl d : D ⊕ Bool) ≠ .inr true by simp), oldEdge,
    Equiv.sumCongr_apply, Sum.map_inl]
  exact Equiv.swap_apply_of_ne_of_ne hmate (show (Sum.inl (P.edge d) : D ⊕ Bool) ≠ .inr true by simp)

noncomputable def degreeTwo : DegreeTwoVertex (map P a) where
  left := .inr false
  right := .inr true
  ne := by simp
  rotation_left := rfl
  rotation_right := rfl
  mate_ne_right := by rw [edge_positive]; simp

@[simp] theorem face_positive : (map P a).face (.inr false) = .inl (P.face a) := by
  rw [RibbonMap.face_apply, edge_positive]
  rfl

@[simp] theorem face_negative : (map P a).face (.inr true) = .inl (P.face (P.edge a)) := by
  rw [RibbonMap.face_apply, edge_negative]
  change (Sum.inl (P.rotation.symm a) : D ⊕ Bool) = Sum.inl (P.rotation.symm (P.edge (P.edge a)))
  rw [P.edge_involutive a]

@[simp] theorem face_anchor : (map P a).face (.inl a) = .inr false := by
  rw [RibbonMap.face_apply, edge_anchor]
  rfl

@[simp] theorem face_mate : (map P a).face (.inl (P.edge a)) = .inr true := by
  rw [RibbonMap.face_apply, edge_mate]
  rfl

theorem face_old (d : D) (ha : d ≠ a) (he : d ≠ P.edge a) :
    (map P a).face (.inl d) = .inl (P.face d) := by
  rw [RibbonMap.face_apply, edge_old P a d ha he]
  rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap
