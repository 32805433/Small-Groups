module

public import SmallPresentation.UniversalGroup.Computability.Machine.PartialRecursiveMachine
public import SmallPresentation.AdianRabin.Computability
public import Mathlib.Computability.Halting

/-! The undecidable fixed program specializes the shared partial-recursive machine compiler. -/

@[expose] public section

namespace UniversalGroup

open Turing Encodable Denumerable

def fixedUniversalEval (n : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code n) 0

theorem fixedUniversalEval_partrec : Partrec fixedUniversalEval :=
  Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp Computable.id)
    (Computable.const 0)

theorem exists_fixed_universal_code :
    ∃ c : ToPartrec.Code, ∀ n,
      (c.eval [n]).Dom ↔ (fixedUniversalEval n).Dom := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code
    (Nat.Partrec'.part_iff₁.mpr fixedUniversalEval_partrec)
  refine ⟨c, fun n => ?_⟩
  have h := hc (n ::ᵥ List.Vector.nil)
  have hv : (n ::ᵥ List.Vector.nil).1 = [n] := by rfl
  rw [hv] at h
  simpa using congrArg Part.Dom h

namespace FixedMachine

abbrev StackColumn := Stack → Option Symbol

noncomputable instance stackColumnPrimcodable : Primcodable StackColumn :=
  Primcodable.ofEquiv (Fin (Fintype.card StackColumn)) (Fintype.equivFin StackColumn)

noncomputable instance tapeSymbolPrimcodable : Primcodable TapeSymbol := by
  change Primcodable (Bool × StackColumn)
  infer_instance

theorem trSingleton_computable :
    Computable fun n => PartrecToTM2.trList [n] :=
  (Computable.list_append.comp trNat_computable
    (Computable.const [PartrecToTM2.Γ'.cons])).of_eq fun n => by
      simp

theorem trInit_main_computable :
    Computable (fun L : List Symbol =>
      @TM2to1.trInit Stack (fun _ : Stack => Symbol)
        inferInstance PartrecToTM2.K'.main L) := by
  let putMain : Symbol → TapeSymbol := fun a =>
    (false, Function.update (fun _ : Stack => none)
      PartrecToTM2.K'.main (some a))
  have hputMain : Computable putMain :=
    (Primrec.dom_finite putMain).to_comp
  have hencoded : Computable fun L : List Symbol =>
      L.reverse.map putMain :=
    (list_map_primrec_of_finite putMain).to_comp.comp Computable.list_reverse
  have hhead : Computable fun L : List Symbol =>
      (L.reverse.map putMain).headI.2 :=
    Computable.snd.comp (Primrec.list_headI.to_comp.comp hencoded)
  have hfirst : Computable fun L : List Symbol =>
      (true, (L.reverse.map putMain).headI.2) :=
    (Computable.const true).pair hhead
  have htail : Computable fun L : List Symbol =>
      (L.reverse.map putMain).tail :=
    Primrec.list_tail.to_comp.comp hencoded
  exact (Computable.list_cons.comp hfirst htail).of_eq fun L => by
    rfl

theorem postInput_computable : Computable postInput :=
  trInit_main_computable.comp trSingleton_computable

theorem postInput_encode_computable :
    Computable fun p : Nat.Partrec.Code => postInput (Encodable.encode p) :=
  postInput_computable.comp Computable.encode

theorem oneTape_halting_not_computable (c : ToPartrec.Code)
    (hc : ∀ n, (c.eval [n]).Dom ↔ (fixedUniversalEval n).Dom) :
    ¬ ComputablePred fun input : List TapeSymbol =>
      (@TM1.eval TapeSymbol OneTapeState (Option Symbol)
        (oneTapeStateInhabited c) inferInstance inferInstance
        oneTapeProgram input).Dom := by
  intro hhalting
  have hencoded : ComputablePred fun p : Nat.Partrec.Code =>
      (@TM1.eval TapeSymbol OneTapeState (Option Symbol)
        (oneTapeStateInhabited c) inferInstance inferInstance
        oneTapeProgram (postInput (Encodable.encode p))).Dom :=
    ComputablePred.computable_of_manyOneReducible
      ⟨fun p => postInput (Encodable.encode p), postInput_encode_computable,
        fun _ => Iff.rfl⟩ hhalting
  apply ComputablePred.halting_problem 0
  exact hencoded.of_eq fun p => by
    let : Inhabited State := stateInhabited c
    let : Inhabited OneTapeState := oneTapeStateInhabited c
    have hdom := (TM2to1.tr_eval_dom PartrecToTM2.tr
      PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode p])).trans
        (tm2_eval_dom_iff c (Encodable.encode p))
    change (TM1.eval oneTapeProgram (postInput (Encodable.encode p))).Dom ↔ _ at hdom
    rw [hdom, hc]
    simp [fixedUniversalEval]

end FixedMachine
end UniversalGroup
