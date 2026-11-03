import Proof.Wire_3_5.UnionMachine.FrontArity
import Proof.Wire_3_5.UnionMachine.FrontKit
import Proof.CaseAnalysis.WitnessOracleCallRun
import Proof.CaseAnalysis.CloseoutScheduleMetadata

/-! # C6 front, U1a: the oracle stage — tag, oracle field and decoded oracle (P3:3669-3672)

Realizes "The weak machine guesses one size-`q^G` general oracle, a class tag, [...] It rejects malformed
descriptions" (P3:3669-3672) for the guess's tag and oracle, in the codec (`decodeGuess`: the tag bit, `readNat`
of the oracle's code, `decodeBooleanCircuit (S.pcp.nativeWidth N)` of it). One machine on its own `OS = 1421` tapes,
from the framed input `x` (tape `0`), the framed witness `w` (tape `1`) and the width `1^q` (tape `2`):

1. base's metadata counter (`CloseoutSchedule.Metadata`: `1^{|w|}`) and the register fill (`FrontFill`);
2. the walker (`FrontOracleField.walkP_spec`): the tag, the verdict on the oracle field, the code's bits framed, the
   rest of the guess framed;
3. the fill from `1^q` and the arity program (`FrontArity.arP_spec`): `frame (binary ℓ q)`;
4. v8's checked oracle call (`CloseoutWitness.OracleCall.call_run`, docked): the exact public decoder flag
   `decodeBooleanCircuit q (value bits)` and the typed native descriptor `PCPPNative.descriptor c`.

Main statement: **`oracle_ready`**. Paper quantity: the guess's tag, its oracle (decoded at arity `q`), and the rest of
the guess. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontOracle
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef
open NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairSource.CloseoutSchedule

/-! ## Layout

`0` input, `1` witness, `2` width `1^q`; `3–9` the counter's scratch; `10` fill marker, `11` walker cell, `12` payload
`P`, `13` rest `R`, `14` tag, `15–24` walker registers; `25` fill marker, `26` arity cell, `27` arity bits, `28–36`
arity registers; `37–1420` the oracle call's cold tapes (its bit tape is `P`). -/

abbrev OS : ℕ := 1421

def mtS (j : Fin 8) : Fin OS := ⟨if j.val = 0 then 1 else 2 + j.val, by have := j.isLt; simp only [OS]; split <;> omega⟩
def wS (j : Fin 15) : Fin OS := ⟨if j.val = 0 then 1 else 10 + j.val, by have := j.isLt; simp only [OS]; split <;> omega⟩
def aS (j : Fin 12) : Fin OS := ⟨if j.val = 0 then 2 else 25 + j.val, by have := j.isLt; simp only [OS]; split <;> omega⟩
def ocS (j : Fin (CloseoutWitness.OracleCall.tapes 3)) : Fin OS :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 27 else if j.val = 2 then 2 else if j.val = 3 then 37
    else if j.val = 4 then 12 else j.val + 33, by
      have := j.isLt; simp only [CloseoutWitness.OracleCall.tapes] at this; simp only [OS]; split_ifs <;> omega⟩

theorem mtS_inj : Function.Injective mtS := by
  intro a b h; have := congrArg Fin.val h; simp only [mtS] at this; apply Fin.ext; split_ifs at this <;> omega
theorem wS_inj : Function.Injective wS := by
  intro a b h; have := congrArg Fin.val h; simp only [wS] at this; apply Fin.ext; split_ifs at this <;> omega
theorem aS_inj : Function.Injective aS := by
  intro a b h; have := congrArg Fin.val h; simp only [aS] at this; apply Fin.ext; split_ifs at this <;> omega
theorem ocS_inj : Function.Injective ocS := by
  intro a b h; have := congrArg Fin.val h; simp only [ocS] at this; apply Fin.ext; split_ifs at this <;> omega

theorem mtS_val (j : Fin 8) : (mtS j).val = if j.val = 0 then 1 else 2 + j.val := rfl
theorem wS_val (j : Fin 15) : (wS j).val = if j.val = 0 then 1 else 10 + j.val := rfl
theorem aS_val (j : Fin 12) : (aS j).val = if j.val = 0 then 2 else 25 + j.val := rfl

theorem mtS_ne (i : Fin OS) (hi : i.val = 0 ∨ i.val = 2 ∨ 10 ≤ i.val) : ∀ j, mtS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; rw [mtS_val] at e; split_ifs at e <;> omega
theorem wS_ne (i : Fin OS) (hi : i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 10) ∨ 25 ≤ i.val) : ∀ j, wS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; rw [wS_val] at e; split_ifs at e <;> omega
theorem aS_ne (i : Fin OS) (hi : i.val < 2 ∨ (2 < i.val ∧ i.val < 26) ∨ 37 ≤ i.val) : ∀ j, aS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; rw [aS_val] at e; split_ifs at e <;> omega
theorem ocS_ne (i : Fin OS) (hi : i.val = 1 ∨ (2 < i.val ∧ i.val < 12) ∨ (12 < i.val ∧ i.val < 27) ∨
    (27 < i.val ∧ i.val < 37)) : ∀ j, ocS j ≠ i := by
  intro j h; have e := congrArg Fin.val h; simp only [ocS] at e; split_ifs at e <;> omega

/-- The walker's registers and the arity program's registers (the fills' targets). -/
def tgtW (i : Fin OS) : Bool := decide (15 ≤ i.val ∧ i.val < 25)
def tgtA (i : Fin OS) : Bool := decide (28 ≤ i.val ∧ i.val < 37)

/-- The decoder's flag and descriptor tapes. -/
def flagO : Fin OS := ocS (CloseoutWitness.OracleCall.parserSlots 3 CloseoutWitness.Oracle.flagSlot)
def descO : Fin OS := ocS (CloseoutWitness.OracleCall.parserSlots 3 CloseoutWitness.Oracle.descriptorSlot)

/-- base's counter: `1^{|w|}` (and scratch) from the framed witness. -/
noncomputable def countM := Composition.machine Metadata.lengthProgram Metadata.copyProgram

/-- **The oracle stage.** -/
noncomputable def osMachine :=
  Composition.machine (RecoveryFocus.machine mtS countM)
  (Composition.machine (FrontFill.fillP (4 : Fin OS) 10 tgtW).compile
  (Composition.machine (cellP (11 : Fin OS)).compile
  (Composition.machine (RecoveryFocus.machine wS FrontOracleField.walkP.toProg.compile)
  (Composition.machine (FrontFill.fillP (2 : Fin OS) 25 tgtA).compile
  (Composition.machine (cellP (26 : Fin OS)).compile
  (Composition.machine (RecoveryFocus.machine aS FrontArity.arP.toProg.compile)
    (RecoveryFocus.machine ocS (CloseoutWitness.OracleCall.machine (id : Fin 3 → Fin 3)))))))))

/-- The stage's input: `frame x`, `frame w`, `1^q`. -/
def osIn (x w : List Bool) (q : ℕ) : Fin OS → List Bool := fun i =>
  if i.val = 0 then frame x else if i.val = 1 then frame w else if i.val = 2 then List.replicate q true else []

/-- The stage's cost. -/
noncomputable def osCost (x w : List Bool) (q : ℕ) : ℕ :=
  (4 * w.length + 5 + 1 + (2 * w.length + 6)) + 1 + ((11 * w.length + 20) + 1 + (1 + 1 +
    (FrontOracleField.walkCost w.length + 1 + ((11 * q + 20) + 1 + (1 + 1 + (FrontArity.arCost q + 1 +
      CloseoutWitness.OracleCall.budget x (payload w.tail) (binary (natBitLength q) q)))))))

/-- **The oracle stage**: the tag on tape `14`, the rest of the guess on `13`, the verdict on the oracle field in the
walker's cell `11`, and v8's decoder flag and descriptor of the field's code at arity `q`; the input, the witness and
the width kept. -/
theorem oracle_ready (x w : List Bool) (q : ℕ) (hN : 2 ≤ x.length) (hw : 16 * w.length ≤ x.length)
    (hℓx : natBitLength q ≤ x.length + 1) (hq : 3 * natBitLength q ≤ q) :
    ∃ out : Fin OS → List Bool, ClockJoin.ReadyRun osMachine (osCost x w q) (osIn x w q) out ∧
      out 14 = [w.headD false] ∧ out 13 = frame (restOf w.tail) ∧ out 11 = [FrontOracleField.okOf w] ∧
      out flagO = [(decodeBooleanCircuit q (value (payload w.tail))).isSome] ∧
      (∀ c : BooleanCircuit q, decodeBooleanCircuit q (value (payload w.tail)) = some c →
        out descO = RepairOrdinary.PCPPNative.descriptor c) ∧
      out 0 = frame x ∧ out 1 = frame w ∧ out 2 = List.replicate q true := by
  set ℓ := natBitLength q with hℓdef
  have hlt : q < 2 ^ ℓ := Round.natBitLength_lt q
  -- 1. `1^{|w|}`
  have g1r : ClockJoin.ReadyRun countM (4 * w.length + 5 + 1 + (2 * w.length + 6)) (Metadata.input w)
      (Metadata.copied w) :=
    ClockJoin.join _ _ _ _ _ _ _ (Metadata.length_run w) (Metadata.copy_run w)
  have g1 := g1r.focus mtS mtS_inj (osIn x w q) (by
    intro j; fin_cases j <;> simp [osIn, mtS, Metadata.input, OS])
  set a1 := install mtS (osIn x w q) (Metadata.copied w) with ha1
  have a1_hi : ∀ i : Fin OS, 10 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (mtS_ne i (by omega))]
    unfold osIn; split_ifs <;> first | rfl | omega
  have a1_0 : a1 0 = frame x := by
    rw [ha1, install_other _ _ _ _ (mtS_ne 0 (by decide))]
    simp [osIn, OS]
  have a1_2 : a1 2 = List.replicate q true := by
    rw [ha1, install_other _ _ _ _ (mtS_ne 2 (by decide))]
    simp [osIn, OS]
  have a1_1 : a1 1 = frame w := by
    rw [ha1, show (1 : Fin OS) = mtS 0 from rfl, install_slot _ mtS_inj]; rfl
  have a1_4 : a1 4 = List.replicate w.length true := by
    rw [ha1, show (4 : Fin OS) = mtS 2 from rfl, install_slot _ mtS_inj]; rfl
  -- 2. the walker's registers
  have hsideW : ∀ i, FrontFill.side 10 tgtW i → 10 ≤ i.val := by
    intro i hi; rcases hi with h | h
    · simp [tgtW] at h; omega
    · rw [h]; decide
  have g2 := fill_ready (4 : Fin OS) 10 tgtW a1 w.length (by decide) (by decide) (by decide) a1_4
    (fun i hi => a1_hi i (hsideW i hi))
  set a2 := (fun i => if FrontFill.side 10 tgtW i then List.replicate (2 * w.length + 3) false else a1 i) with ha2
  have a2_other : ∀ i : Fin OS, (i.val < 10 ∨ 25 ≤ i.val ∨ (10 < i.val ∧ i.val < 15)) → a2 i = a1 i := by
    intro i hi
    rw [ha2]; simp only
    rw [if_neg]
    rintro (h | h)
    · simp [tgtW] at h; omega
    · rw [h] at hi; simp [OS] at hi
  -- 3. the walker's cell
  have g3 := cell_ready (11 : Fin OS) a2 (by rw [a2_other _ (by decide)]; exact a1_hi _ (by decide))
  set a3 := Function.update a2 (11 : Fin OS) [false] with ha3
  -- 4. the walker
  set cap := 2 * w.length + 2 with hcap
  have hwk := FrontOracleField.walkP_spec cap w false le_rfl
  have g4r := wm_ready _ cap _ _ _ hwk (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
  have g4 := g4r.focus wS wS_inj a3 (by
    intro j
    fin_cases j
    · show a3 1 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_1]; rfl
    · show a3 11 = _
      rw [ha3, Function.update_self]; rfl
    · show a3 12 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_hi _ (by decide)]; rfl
    · show a3 13 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_hi _ (by decide)]; rfl
    · show a3 14 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_hi _ (by decide)]; rfl
    all_goals
      (rw [ha3, Function.update_of_ne (by decide)]
       simp [ha2, FrontFill.side, tgtW, wS, wenc, role, FrontOracleField.st, FrontOracleField.d0, regTape_zero,
         hcap]))
  set a4 := install wS a3 (wenc cap (FrontOracleField.st w (FrontOracleField.dF w))).A with ha4
  have a4_out : ∀ j, a4 (wS j) = (wenc cap (FrontOracleField.st w (FrontOracleField.dF w))).A j :=
    fun j => install_slot _ wS_inj _ _ j
  have a4_other : ∀ i : Fin OS, (i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 10) ∨ 25 ≤ i.val) → a4 i = a3 i := by
    intro i hi
    rw [ha4, install_other _ _ _ _ (wS_ne i hi)]
  -- 5. the arity registers
  have hsideA : ∀ i, FrontFill.side 25 tgtA i → 25 ≤ i.val := by
    intro i hi; rcases hi with h | h
    · simp [tgtA] at h; omega
    · rw [h]; decide
  have a4_2 : a4 2 = List.replicate q true := by
    rw [a4_other _ (by decide), ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_2]
  have a4_hi : ∀ i : Fin OS, 25 ≤ i.val → a4 i = [] := by
    intro i hi
    rw [a4_other _ (by omega), ha3, Function.update_of_ne (by intro h; rw [h] at hi; simp [OS] at hi),
      a2_other _ (by omega), a1_hi _ (by omega)]
  have g5 := fill_ready (2 : Fin OS) 25 tgtA a4 q (by decide) (by decide) (by decide) a4_2
    (fun i hi => a4_hi i (hsideA i hi))
  set a5 := (fun i => if FrontFill.side 25 tgtA i then List.replicate (2 * q + 3) false else a4 i) with ha5
  have a5_other : ∀ i : Fin OS, (i.val < 25 ∨ 37 ≤ i.val ∨ (25 < i.val ∧ i.val < 28)) → a5 i = a4 i := by
    intro i hi
    rw [ha5]; simp only
    rw [if_neg]
    rintro (h | h)
    · simp [tgtA] at h; omega
    · rw [h] at hi; simp [OS] at hi
  -- 6. the arity cell
  have g6 := cell_ready (26 : Fin OS) a5 (by rw [a5_other _ (by decide)]; exact a4_hi _ (by decide))
  set a6 := Function.update a5 (26 : Fin OS) [false] with ha6
  -- 7. the arity bits
  set capA := 2 * q + 2 with hcapA
  have har := FrontArity.arP_spec q false capA (by omega)
  have g7r := wm_ready _ capA _ _ _ har (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
  have g7 := g7r.focus aS aS_inj a6 (by
    intro j
    fin_cases j
    · show a6 2 = _
      rw [ha6, Function.update_of_ne (by decide), a5_other _ (by decide), a4_2]; rfl
    · show a6 26 = _
      rw [ha6, Function.update_self]; rfl
    · show a6 27 = _
      rw [ha6, Function.update_of_ne (by decide), a5_other _ (by decide), a4_hi _ (by decide)]; rfl
    all_goals
      (rw [ha6, Function.update_of_ne (by decide)]
       simp [ha5, FrontFill.side, tgtA, aS, wenc, role, FrontArity.arIn, regTape_zero, hcapA]))
  set a7 := install aS a6 (wenc capA (FrontArity.arOut q false)).A with ha7
  have a7_other : ∀ i : Fin OS, (i.val < 2 ∨ (2 < i.val ∧ i.val < 26) ∨ 37 ≤ i.val) → a7 i = a6 i := by
    intro i hi
    rw [ha7, install_other _ _ _ _ (aS_ne i hi)]
  -- the walker's outputs survive stages 5–7
  have keep : ∀ i : Fin OS, (i.val = 0 ∨ i.val = 1 ∨ (10 < i.val ∧ i.val < 25)) → a7 i = a4 i := by
    intro i hi
    rw [a7_other _ (by omega), ha6, Function.update_of_ne (by intro h; rw [h] at hi; simp [OS] at hi),
      a5_other _ (by omega)]
  -- 8. the oracle call
  have hval : value (binary ℓ q) = q := binary_value ℓ q hlt
  have hpl : (payload w.tail).length ≤ w.length := by
    have := List.length_take_le (ones w.tail) (w.tail.drop (ones w.tail + 1))
    have h2 := ones_le w.tail
    simp [payload] at this ⊢ <;> omega
  set base : Fin 3 → List Bool := ![frame x, frame (binary ℓ q), List.replicate q true] with hbase
  obtain ⟨o8, g8r, hkeep8, hflag, hdesc⟩ := CloseoutWitness.OracleCall.call_run (id : Fin 3 → Fin 3) base
    (payload w.tail) x (binary ℓ q) rfl rfl (by simp [hbase, hval]) hN (by omega) (by simp [binary_length]; omega)
  rw [hval] at hflag hdesc
  have a7_12 : a7 12 = frame (payload w.tail) := by
    rw [keep _ (by decide), show (12 : Fin OS) = wS 2 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF, frame]
  have g8 := g8r.focus ocS ocS_inj a7 (by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [show Fin.castAdd 1385 i = CloseoutWitness.OracleCall.old i from rfl, CloseoutWitness.OracleCall.input_old]
      fin_cases i
      · show a7 0 = _; rw [keep _ (by decide), a4_other _ (by decide), ha3, Function.update_of_ne (by decide),
          a2_other _ (by decide), a1_0]; rfl
      · show a7 27 = _
        rw [ha7, show (27 : Fin OS) = aS 2 from rfl, install_slot _ aS_inj]
        simp [wenc, role, FrontArity.arOut, hbase, hℓdef]
      · show a7 2 = _
        rw [ha7, show (2 : Fin OS) = aS 0 from rfl, install_slot _ aS_inj]
        simp [wenc, role, FrontArity.arOut, hbase]
    · rw [show Fin.natAdd 3 i = CloseoutWitness.OracleCall.extra 3 i from rfl, CloseoutWitness.OracleCall.input_extra]
      by_cases hi1 : i.val = 1
      · rw [if_pos hi1]
        have e : ocS (CloseoutWitness.OracleCall.extra 3 i) = 12 := by
          apply Fin.ext; simp [ocS, CloseoutWitness.OracleCall.extra, hi1, OS]
        rw [e, a7_12]
      · rw [if_neg hi1]
        have hv : 37 ≤ (ocS (CloseoutWitness.OracleCall.extra 3 i)).val := by
          simp only [ocS, CloseoutWitness.OracleCall.extra, Fin.val_natAdd]; split_ifs <;> omega
        rw [a7_other _ (by omega), ha6, Function.update_of_ne (by intro h; rw [h] at hv; simp [OS] at hv),
          a5_other _ (by omega)]
        exact a4_hi _ (by omega))
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 (ClockJoin.join _ _ _ _ _ _ _ g4 (ClockJoin.join _ _ _ _ _ _ _ g5
    (ClockJoin.join _ _ _ _ _ _ _ g6 (ClockJoin.join _ _ _ _ _ _ _ g7 g8))))))) (by simp [osCost, hℓdef]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the outputs
  · rw [install_other _ _ _ _ (ocS_ne 14 (by decide)),
      keep _ (by decide), show (14 : Fin OS) = wS 4 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [install_other _ _ _ _ (ocS_ne 13 (by decide)),
      keep _ (by decide), show (13 : Fin OS) = wS 3 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [install_other _ _ _ _ (ocS_ne 11 (by decide)),
      keep _ (by decide), show (11 : Fin OS) = wS 1 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [flagO, install_slot _ ocS_inj]; exact hflag
  · intro c hc; rw [descO, install_slot _ ocS_inj]; exact hdesc c hc
  · rw [show (0 : Fin OS) = ocS (CloseoutWitness.OracleCall.old 0) from rfl, install_slot _ ocS_inj, hkeep8]; rfl
  · rw [install_other _ _ _ _ (ocS_ne 1 (by decide)),
      keep _ (by decide), show (1 : Fin OS) = wS 0 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st]
  · rw [show (2 : Fin OS) = ocS (CloseoutWitness.OracleCall.old 2) from rfl, install_slot _ ocS_inj, hkeep8]; rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FrontOracle
