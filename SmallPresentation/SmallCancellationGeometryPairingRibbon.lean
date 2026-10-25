module

public import SmallPresentation.SmallCancellationGeometryPairing
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# From boundary matchings to actual ribbon maps

The cap-insertion matching determines a fixed-point-free involution on the actual positions of
the original boundary word. Its vertex rotation is the cyclic order of those positions. The
construction keeps the proven noncrossing endpoint certificate. A topological realization or
an Euler-characteristic theorem for these maps is not assumed or asserted here.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing

variable {X : Type*} {w : List (SignedLetter X)} (P : BoundaryPairing w)

/-- Each recorded arc has two distinguished dart ends. -/
abbrev ArcDart := Fin P.arcs.length × Bool

/-- The actual position of an arc end in the original word. -/
def position (d : P.ArcDart) : Fin w.length := by
  let arc := P.arcs[d.1]
  have hb := P.arcs_bounded arc (List.getElem_mem d.1.isLt)
  exact if d.2 then ⟨arc.2, hb.2⟩ else ⟨arc.1, hb.1⟩

/-- Location of an arc end in the flattened list of recorded endpoints. -/
def slot (d : P.ArcDart) : ℕ := 2 * d.1.val + if d.2 then 1 else 0

private theorem flatPairs_even (pairs : List (ℕ × ℕ)) (i : ℕ) :
    (pairs.flatMap (fun arc ↦ [arc.1, arc.2]))[2 * i]? = (pairs[i]?).map Prod.fst := by
  induction pairs generalizing i with
  | nil => simp
  | cons arc rest ih =>
    cases i with
    | zero => simp
    | succ i => simpa [Nat.mul_succ, Nat.add_assoc] using ih i

private theorem flatPairs_odd (pairs : List (ℕ × ℕ)) (i : ℕ) :
    (pairs.flatMap (fun arc ↦ [arc.1, arc.2]))[2 * i + 1]? =
      (pairs[i]?).map Prod.snd := by
  induction pairs generalizing i with
  | nil => simp
  | cons arc rest ih =>
    cases i with
    | zero => simp
    | succ i => simpa [Nat.mul_succ, Nat.add_assoc] using ih i

/-- The source enumeration and the actual word position refer to the same endpoint. -/
theorem endpoints_slot (d : P.ArcDart) : P.endpoints[P.slot d]? = some (P.position d).val := by
  rcases d with ⟨i, b⟩
  cases b <;> simp [slot, position, endpoints, flatPairs_even, flatPairs_odd]

theorem slot_lt (d : P.ArcDart) : P.slot d < P.endpoints.length := by
  have hl := P.twice_arcs_length
  have hpos := d.1.isLt
  rw [P.endpoints_length]
  unfold slot
  split_ifs <;> omega

/-- The flattened endpoint list has no duplicates, so distinct arc ends have distinct positions. -/
theorem position_injective : Function.Injective P.position := by
  intro d e h
  have hs : P.slot d = P.slot e := P.endpoints_nodup.eq_of_getElem?_eq (P.slot_lt d)
    (by rw [P.endpoints_slot, P.endpoints_slot, h])
  rcases d with ⟨i, bi⟩
  rcases e with ⟨j, bj⟩
  cases bi <;> cases bj <;> simp only [slot, Bool.false_eq_true, ite_false, ite_true] at hs
  all_goals
    have hij : i = j := Fin.ext (by omega)
    subst j
    first | rfl | omega

/-- The source has exactly one dart for each boundary position, so the position map is bijective. -/
theorem position_bijective : Function.Bijective P.position := by
  apply (Fintype.bijective_iff_injective_and_card P.position).mpr
  refine ⟨P.position_injective, ?_⟩
  simpa only [ArcDart, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
    using P.twice_arcs_length

/-- Identify abstract arc ends with the actual finite ordered boundary positions. -/
noncomputable def positionEquiv : P.ArcDart ≃ Fin w.length :=
  Equiv.ofBijective P.position P.position_bijective

@[simp] theorem positionEquiv_apply (d : P.ArcDart) : P.positionEquiv d = P.position d := rfl

/-- Reverse the two ends of a recorded arc. -/
def reverseDart : Equiv.Perm P.ArcDart where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by cases d; simp
  right_inv d := by cases d; simp

@[simp] theorem reverseDart_apply (d : P.ArcDart) : P.reverseDart d = (d.1, !d.2) := rfl

theorem reverseDart_involutive : Function.Involutive P.reverseDart := by
  intro d
  cases d
  simp

theorem reverseDart_ne (d : P.ArcDart) : P.reverseDart d ≠ d := by
  intro h
  have hb := congrArg Prod.snd h
  change Bool.not d.2 = d.2 at hb
  cases hbit : d.2 <;> simp [hbit] at hb

/-- The matching as an actual ribbon map on positions of the boundary word. -/
noncomputable def ribbon : RibbonMap (Fin w.length) where
  edge := P.positionEquiv.symm.trans (P.reverseDart.trans P.positionEquiv)
  edge_involutive d := by
    change P.positionEquiv (P.reverseDart (P.positionEquiv.symm
      (P.positionEquiv (P.reverseDart (P.positionEquiv.symm d))))) = d
    rw [Equiv.symm_apply_apply, P.reverseDart_involutive, Equiv.apply_symm_apply]
  edge_ne d h := by
    apply P.reverseDart_ne (P.positionEquiv.symm d)
    apply P.positionEquiv.injective
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using h
  rotation := finRotate w.length

/-- The pairing involution sends each selected arc end to the other end of that same arc. -/
@[simp] theorem ribbon_edge_position (d : P.ArcDart) :
    P.ribbon.edge (P.position d) = P.position (P.reverseDart d) := by
  change P.positionEquiv (P.reverseDart (P.positionEquiv.symm (P.positionEquiv d))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem ribbon_rotation : P.ribbon.rotation = finRotate w.length := rfl

/-- Each explicit chord is an edge of the constructed ribbon map. -/
theorem ribbon_edge_left (i : Fin P.arcs.length) :
    P.ribbon.edge (P.position (i, false)) = P.position (i, true) :=
  P.ribbon_edge_position (i, false)

/-- The actual pairing involution has no crossing chords in boundary order. -/
theorem ribbon_noncrossing (d e : Fin w.length)
    (hd : d.val < (P.ribbon.edge d).val) (he : e.val < (P.ribbon.edge e).val) :
    ¬(d.val < e.val ∧ e.val < (P.ribbon.edge d).val ∧
      (P.ribbon.edge d).val < (P.ribbon.edge e).val) := by
  obtain ⟨⟨i, bi⟩, rfl⟩ := P.position_bijective.surjective d
  obtain ⟨⟨j, bj⟩, rfl⟩ := P.position_bijective.surjective e
  have hi := P.arcs_ordered P.arcs[i] (List.getElem_mem i.isLt)
  have hj := P.arcs_ordered P.arcs[j] (List.getElem_mem j.isLt)
  simp only [P.ribbon_edge_position] at hd he ⊢
  cases bi <;> cases bj <;>
    simp only [position, reverseDart_apply, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] at hd he ⊢
  · exact P.arcs_noncrossing P.arcs[i] (List.getElem_mem i.isLt)
      P.arcs[j] (List.getElem_mem j.isLt)
  all_goals omega

/-- The new cap of an insertion is an actual adjacent edge of the constructed ribbon. -/
theorem inserted_cap_edge (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) :
    let new := BoundaryPairing.insert before after x sign old
    new.ribbon.edge ⟨before.length, by simp⟩ =
      ⟨before.length + 1, by simp⟩ := by
  dsimp only
  let new := BoundaryPairing.insert before after x sign old
  let i : Fin new.arcs.length := ⟨0, by simp [new, arcs]⟩
  simpa [position, new, arcs, i] using new.ribbon_edge_left i

/-- An adjacent non-wrapping matched pair bounds a one-corner face in the actual ribbon. -/
theorem face_fixed_of_adjacent (d : Fin w.length) (hbound : d.val + 1 < w.length)
    (hedge : (P.ribbon.edge d).val = d.val + 1) : P.ribbon.face d = d := by
  have he : P.ribbon.edge d = P.ribbon.rotation d := by
    apply Fin.ext
    rw [hedge]
    change d.val + 1 = (finRotate w.length d).val
    simp only [finRotate_apply, Fin.add_def]
    change d.val + 1 = (d.val + (1 % w.length)) % w.length
    have hn : 1 < w.length := by omega
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hbound]
  change P.ribbon.rotation.symm (P.ribbon.edge d) = d
  rw [he, Equiv.symm_apply_apply]

/-- The inserted cap creates an actual singleton face cycle. This is a local fact;
the separate Euler-preservation argument must still track all other face cycles. -/
theorem inserted_cap_face_length (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) :
    let new := BoundaryPairing.insert before after x sign old
    (new.ribbon.faceBoundary ⟨before.length, by simp⟩).length = 1 := by
  dsimp only
  let new := BoundaryPairing.insert before after x sign old
  let d : Fin (before ++ (x, sign) :: (x, !sign) :: after).length :=
    ⟨before.length, by simp⟩
  have he : (new.ribbon.edge d).val = d.val + 1 := by
    have h := inserted_cap_edge before after x sign old
    exact congrArg Fin.val h
  have hb : d.val + 1 < (before ++ (x, sign) :: (x, !sign) :: after).length := by
    simp only [d, List.length_append, List.length_cons]
    omega
  have hf := new.face_fixed_of_adjacent d hb he
  exact (new.ribbon.faceBoundary_length d).trans
    (Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hf)

/-- Reading a finite boundary coordinate recovers its optional list lookup. -/
private theorem letter_lookup (d : Fin w.length) : w[d.val]? = some (w.get d) := by
  simp

/-- The actual edge involution pairs inverse letters of the original word. -/
theorem ribbon_edge_letter (d : Fin w.length) : w[P.ribbon.edge d] = reverseLetter w[d] := by
  obtain ⟨⟨i, b⟩, rfl⟩ := P.position_bijective.surjective d
  change w.get (P.ribbon.edge (P.position (i, b))) =
    reverseLetter (w.get (P.position (i, b)))
  rw [P.ribbon_edge_position]
  obtain ⟨x, sign, hl, hr⟩ := P.arcs_inverse_labels P.arcs[i] (List.getElem_mem i.isLt)
  have hleft : w.get (P.position (i, false)) = (x, sign) := by
    apply Option.some.inj
    rw [← letter_lookup]
    exact hl
  have hright : w.get (P.position (i, true)) = (x, !sign) := by
    apply Option.some.inj
    rw [← letter_lookup]
    exact hr
  cases b <;> simp only [reverseDart_apply, Bool.not_false, Bool.not_true, hleft, hright,
    reverseLetter, Bool.not_not]

/-- The pairing ribbon has the actual word letters as its arc labels and trivial coefficients. -/
noncomputable def labelling : RibbonLabelling P.ribbon X PUnit where
  arc d := w[d]
  corner _ := PUnit.unit
  edge_arc := P.ribbon_edge_letter

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing
