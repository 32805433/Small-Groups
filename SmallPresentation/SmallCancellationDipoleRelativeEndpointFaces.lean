module

public import SmallPresentation.SmallCancellationDipoleRelativeSuppression
public import SmallPresentation.SmallCancellationGeometryRelativeRestriction

/-!
# Full corridor suppression preserves the original coefficient region equations

All non-endpoint coefficients are one. Delete actual degree-two corridor vertices, removing
isolated closed bands when necessary. The first-return ribbon retains the entire ordered
product on each surviving original face. The theorem is independent of planarity.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem

universe u v
variable {X : Type v} {H : Type*} [Group H]

private theorem endpoint_face_product_aux (n : ℕ) :
    ∀ (D : Type u) (_ : Fintype D) (B : BandSystem D X) (P : RibbonMap D)
      (_hcap : ∀ d, B.cap d = P.edge d)
      (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)
      (w : D → H) (_hw : ∀ d, B.corridor d ≠ d → w d = 1),
      Fintype.card D = n → ∀ d : B.Endpoint,
      (((B.endpointRibbon P hrot).faceBoundary d).map (fun a ↦ w a.val)).prod =
        ((P.faceBoundary d.val).map w).prod := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D inst B P hcap hrot w hw hn d
    classical
    by_cases hfix : ∀ d, B.corridor d = d
    · exact RibbonMap.face_product_relabel (B.endpointRibbon P hrot) P
        (B.allEndpointsEquiv hfix)
        (fun a ↦ (B.endpoint_val_of_all_fixed hfix a).trans (hcap a.val))
        (fun _ ↦ rfl) w d
    · push Not at hfix
      obtain ⟨a, ha⟩ := hfix
      let b := B.corridor a
      have hab : a ≠ b := ha.symm
      have hba : B.corridor b = a := B.corridor_involutive a
      have hb : B.corridor b ≠ b := by rw [hba]; exact hab
      have hr₁ : P.rotation a = b := hrot a ha
      have hr₂ : P.rotation b = a := (hrot b hb).trans hba
      by_cases he : P.edge a = b
      · let p : D → Prop := fun x ↦ x ≠ a ∧ x ≠ b
        have hpair (σ : Equiv.Perm D) (h₁ : σ a = b) (h₂ : σ b = a) (x : D) :
            p (σ x) ↔ p x := by
          simpa only [p, not_or] using
            not_congr (PermutationCycles.twoCycle_invariant σ a b h₁ h₂ x)
        have hcorr : ∀ x, p (B.corridor x) ↔ p x := hpair B.corridor rfl hba
        have hrotation : ∀ x, p (P.rotation x) ↔ p x := hpair P.rotation hr₁ hr₂
        have hcap' : ∀ x, p (B.cap x) ↔ p x := by
          intro x
          rw [hcap]
          exact hpair P.edge he (by rw [← he, P.edge_involutive]) x
        have hp : ∀ x : B.Endpoint, p x.val := by
          intro x
          constructor
          · intro hx
            exact ha (hx ▸ x.property)
          · intro hx
            exact hb (hx ▸ x.property)
        let B' := B.restricted p hcap' hcorr
        let P' := P.restrict p (B.restricted_cap_invariant p hcap' P hcap) hrotation
        have hcap'' (x : {x : D // p x}) : B'.cap x = P'.edge x :=
          Subtype.ext (hcap x.val)
        have hrot' := B.restricted_rotation p hcap' hcorr P hcap hrotation hrot
        have hw' (x : {x : D // p x}) (hx : B'.corridor x ≠ x) : w x.val = 1 :=
          hw x.val (fun hh ↦ hx (Subtype.ext hh))
        have hlt : Fintype.card {x : D // p x} < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := a) (fun h ↦ h.1 rfl)
        let e := B.restrictedEndpointsEquiv p hcap' hcorr hp
        have hi := ih _ hlt _ inferInstance B' P' hcap'' hrot'
          (fun x ↦ w x.val) hw' rfl (e d)
        have ht := RibbonMap.face_product_relabel (B.endpointRibbon P hrot)
          (B'.endpointRibbon P' hrot') e
          (B.restrictedEndpointsEquiv_pairing p hcap' hcorr hp) (fun _ ↦ rfl)
          (fun x ↦ w x.val.val) d
        calc
          _ = (((B'.endpointRibbon P' hrot').faceBoundary (e d)).map
              (fun x ↦ w x.val.val)).prod := ht
          _ = ((P'.faceBoundary (e d).val).map (fun x ↦ w x.val)).prod := hi
          _ = ((P.faceBoundary d.val).map w).prod := by
            change ((P'.faceBoundary (e d).val).map (w ∘ Subtype.val)).prod = _
            rw [← List.map_map, P.restrict_faceBoundary]
            rfl
      · let C : DegreeTwoVertex P := ⟨a, b, hab, hr₁, hr₂, he⟩
        have hl : B.corridor C.left = C.right := rfl
        let B' := C.suppressedBands B hcap hl
        have hcap' (x : C.Dart) : B'.cap x = C.suppress.edge x := rfl
        have hrot' := C.suppressed_rotation B hcap hl hrot
        have hw' (x : C.Dart) (hx : B'.corridor x ≠ x) : w x.val = 1 :=
          hw x.val (fun hh ↦ hx (Subtype.ext hh))
        have hlt : Fintype.card C.Dart < n := by
          have hh : Fintype.card D = Fintype.card C.Dart + 2 := by
            simpa only [Fintype.card_eq_nat_card] using C.dualBigon.card_darts
          omega
        let e := C.endpointsEquiv B hcap hl
        have hi := ih _ hlt _ inferInstance B' C.suppress hcap' hrot'
          (fun x ↦ w x.val) hw' rfl (e d)
        have hrotation (x : B.Endpoint) :
            e ((B.endpointRibbon P hrot).rotation x) =
              (B'.endpointRibbon C.suppress hrot').rotation (e x) := by
          apply Subtype.ext
          apply Subtype.ext
          exact (C.rotation_val (C.endpointSurvives B hl x)).symm
        have ht := RibbonMap.face_product_relabel (B.endpointRibbon P hrot)
          (B'.endpointRibbon C.suppress hrot') e
          (C.endpointsEquiv_pairing B hcap hl) hrotation (fun x ↦ w x.val.val) d
        calc
          _ = (((B'.endpointRibbon C.suppress hrot').faceBoundary (e d)).map
              (fun x ↦ w x.val.val)).prod := ht
          _ = ((C.suppress.faceBoundary (e d).val).map (fun x ↦ w x.val)).prod := hi
          _ = ((P.faceBoundary d.val).map w).prod :=
            C.suppress_face_product w (hw a ha) (hw b hb) (e d).val

/-- Suppressing any finite collection of coefficient-one corridor interiors preserves the
entire noncommutative product on every surviving region boundary. -/
theorem endpoint_face_product {D : Type u} [Fintype D] (B : BandSystem D X)
    (P : RibbonMap D) (hcap : ∀ d, B.cap d = P.edge d)
    (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)
    (w : D → H) (hw : ∀ d, B.corridor d ≠ d → w d = 1) (d : B.Endpoint) :
    (((B.endpointRibbon P hrot).faceBoundary d).map (fun a ↦ w a.val)).prod =
      ((P.faceBoundary d.val).map w).prod :=
  endpoint_face_product_aux (Fintype.card D) D inferInstance B P hcap hrot w hw rfl d

/-- The relative labels on the actual first-return endpoints retain each original region value. -/
theorem endpoint_faceValue {D : Type u} [Fintype D] (B : BandSystem D X)
    (P : RibbonMap D) (L : RibbonLabelling P X H)
    (hrot : ∀ d, B.corridor d ≠ d → P.rotation d = B.corridor d)
    (hread : ∀ d, B.letter d = L.arc d)
    (hcap : ∀ d, B.cap d = P.edge d)
    (hw : ∀ d, B.corridor d ≠ d → L.corner d = 1) (d : B.Endpoint) :
    (B.endpointLabelling P L hrot hread).faceValue d = L.faceValue d.val := by
  exact B.endpoint_face_product P hcap hrot (fun a ↦ (L.corner a)⁻¹)
    (fun a ha ↦ by rw [hw a ha, inv_one]) d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BandSystem
