import Proof.Wire_3_5.UnionMachine.FrontKit
import Proof.Wire_3_5.UnionMachine.FrontSize

/-! # C6 front, U1a: the oracle's size check as a stage (P3:3669)

Docks the size check (`FrontSize.sizeP_true` / `sizeP_false`) as one machine on its own `19` tapes, from the framed
input `x` (tape `0`, only counted), the Theorem 2.5 repository's decoder flag `[o.isSome]` (tape `1`), the raw descriptor (tape `2`) and the
width `1^q` (tape `3`): base's metadata counter (`1^{|x|}`), the register fill (`FrontFill`), the cell, the check. Its
cell (tape `12`) is `sizeVerdict G q o`: `decide (c.size ≤ oracleSizeBound G q)` for the decoded oracle `o = some c`
(whose descriptor is on tape `2`), `false` when nothing decoded.
Main statement: **`size_ready`**. Paper quantity: the oracle's size bound `|O| ≤ q^G`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSizeStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontKit
open NearCubicWires.RepairSource.CloseoutSchedule

/-- The size verdict on a decoded oracle (`false` when nothing decoded). -/
def sizeVerdict (G q : ℕ) : Option (BooleanCircuit q) → Bool
  | none => false
  | some c => decide (c.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G q)

/-! ## Layout: `0` input, `1` flag, `2` descriptor, `3` width; `4–10` counter scratch; `11` fill marker; `12` cell;
`13–18` registers -/

abbrev ST : ℕ := 19

def mtS (j : Fin 8) : Fin ST := ⟨if j.val = 0 then 0 else 3 + j.val, by have := j.isLt; simp only [ST]; split <;> omega⟩
def sS (j : Fin 10) : Fin ST := ⟨if j.val = 0 then 1 else if j.val = 1 then 12 else if j.val ≤ 3 then j.val
  else 9 + j.val, by have := j.isLt; simp only [ST]; split_ifs <;> omega⟩

theorem mtS_inj : Function.Injective mtS := by
  intro a b h; have := congrArg Fin.val h; simp only [mtS] at this; apply Fin.ext; split_ifs at this <;> omega
theorem sS_inj : Function.Injective sS := by
  intro a b h; have := congrArg Fin.val h; simp only [sS] at this; apply Fin.ext; split_ifs at this <;> omega

theorem mtS_ne (i : Fin ST) (hi : (1 ≤ i.val ∧ i.val ≤ 3) ∨ 11 ≤ i.val) : ∀ j, mtS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; simp only [mtS] at e; split_ifs at e <;> omega
theorem sS_ne (i : Fin ST) (hi : i.val = 0 ∨ (4 ≤ i.val ∧ i.val ≤ 11)) : ∀ j, sS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; simp only [sS] at e; split_ifs at e <;> omega

def tgtS (i : Fin ST) : Bool := decide (13 ≤ i.val)

noncomputable def countM := Composition.machine Metadata.lengthProgram Metadata.copyProgram

/-- **The size stage** at `Dg` divisions. -/
noncomputable def ssMachine (Dg : ℕ) :=
  Composition.machine (RecoveryFocus.machine mtS countM)
  (Composition.machine (FrontFill.fillP (5 : Fin ST) 11 tgtS).compile
  (Composition.machine (FrontKit.cellP (12 : Fin ST)).compile
    (RecoveryFocus.machine sS (FrontSize.sizeP Dg).toProg.compile)))

def ssIn (x : List Bool) (b : Bool) (desc : List Bool) (q : ℕ) : Fin ST → List Bool := fun i =>
  if i.val = 0 then frame x else if i.val = 1 then [b] else if i.val = 2 then desc
  else if i.val = 3 then List.replicate q true else []

noncomputable def ssCost (x : List Bool) (Dg : ℕ) : ℕ :=
  (4 * x.length + 5 + 1 + (2 * x.length + 6)) + 1 + ((11 * x.length + 20) + 1 + (1 + 1 +
    FrontSize.sizeCost (2 * x.length + 2) Dg))

/-- **The size stage**: its cell (tape `12`) is the size verdict of the decoded oracle `o` (descriptor on tape `2`);
the input, the flag, the descriptor and the width kept. -/
theorem size_ready (x : List Bool) (q G : ℕ) (o : Option (BooleanCircuit q)) (desc : List Bool)
    (hdesc : ∀ c, o = some c → desc = PCPPNative.descriptor c)
    (hx1 : ∀ c : BooleanCircuit q, o = some c → c.size + 1 ≤ 2 * x.length + 2)
    (hx2 : ∀ c : BooleanCircuit q, o = some c → 2 * natBitLength q + 2 * natBitLength c.size + 2 ≤ 2 * x.length + 2) :
    ∃ out : Fin ST → List Bool,
      ClockJoin.ReadyRun (ssMachine (2 ^ RecoveryScheduleEnvelope.oracleDepth G))
        (ssCost x (2 ^ RecoveryScheduleEnvelope.oracleDepth G)) (ssIn x o.isSome desc q) out ∧
      out 12 = [sizeVerdict G q o] ∧ out 0 = frame x ∧ out 1 = [o.isSome] ∧ out 2 = desc ∧
      out 3 = List.replicate q true := by
  set Dg := 2 ^ RecoveryScheduleEnvelope.oracleDepth G with hDg
  -- 1. `1^{|x|}`
  have g1r : ClockJoin.ReadyRun countM (4 * x.length + 5 + 1 + (2 * x.length + 6)) (Metadata.input x)
      (Metadata.copied x) :=
    ClockJoin.join _ _ _ _ _ _ _ (Metadata.length_run x) (Metadata.copy_run x)
  have g1 := g1r.focus mtS mtS_inj (ssIn x o.isSome desc q) (by
    intro j; fin_cases j <;> simp [ssIn, mtS, Metadata.input, ST])
  set a1 := install mtS (ssIn x o.isSome desc q) (Metadata.copied x) with ha1
  have a1_hi : ∀ i : Fin ST, 11 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (mtS_ne i (by omega))]
    unfold ssIn; split_ifs <;> first | rfl | omega
  have a1_1 : a1 1 = [o.isSome] := by rw [ha1, install_other _ _ _ _ (mtS_ne 1 (by decide))]; simp [ssIn, ST]
  have a1_2 : a1 2 = desc := by rw [ha1, install_other _ _ _ _ (mtS_ne 2 (by decide))]; simp [ssIn, ST]
  have a1_3 : a1 3 = List.replicate q true := by
    rw [ha1, install_other _ _ _ _ (mtS_ne 3 (by decide))]; simp [ssIn, ST]
  have a1_0 : a1 0 = frame x := by rw [ha1, show (0 : Fin ST) = mtS 0 from rfl, install_slot _ mtS_inj]; rfl
  have a1_5 : a1 5 = List.replicate x.length true := by
    rw [ha1, show (5 : Fin ST) = mtS 2 from rfl, install_slot _ mtS_inj]; rfl
  -- 2. the registers
  have hside : ∀ i, FrontFill.side 11 tgtS i → 11 ≤ i.val := by
    intro i hi; rcases hi with h | h
    · simp [tgtS] at h; omega
    · rw [h]; decide
  have g2 := fill_ready (5 : Fin ST) 11 tgtS a1 x.length (by decide) (by decide) (by decide) a1_5
    (fun i hi => a1_hi i (hside i hi))
  set a2 := (fun i => if FrontFill.side 11 tgtS i then List.replicate (2 * x.length + 3) false else a1 i) with ha2
  have a2_other : ∀ i : Fin ST, (i.val < 11 ∨ i.val = 12) → a2 i = a1 i := by
    intro i hi
    rw [ha2]; simp only
    rw [if_neg]
    rintro (h | h)
    · simp [tgtS] at h; omega
    · rw [h] at hi; simp [ST] at hi
  -- 3. the cell
  have g3 := cell_ready (12 : Fin ST) a2 (by rw [a2_other _ (by decide)]; exact a1_hi _ (by decide))
  set a3 := Function.update a2 (12 : Fin ST) [false] with ha3
  -- 4. the check
  set cap := 2 * x.length + 2 with hcap
  obtain ⟨n, hn, hwm, hfin⟩ : ∃ n, n ≤ FrontSize.sizeCost cap Dg ∧
      WExec cap (FrontSize.sizeP Dg) (FrontSize.st o.isSome desc q FrontSize.d0)
        (FrontSize.st o.isSome desc q (FrontSize.dF (sizeVerdict G q o))) n ∧ True := by
    cases ho : o with
    | none =>
      exact ⟨2, by unfold FrontSize.sizeCost; omega, FrontSize.sizeP_false cap desc q Dg, trivial⟩
    | some c =>
      have hd := hdesc c ho
      subst hd
      obtain ⟨n, hn, h⟩ := FrontSize.sizeP_true cap q G c (hx1 c ho) (hx2 c ho)
      exact ⟨n, hn, h, trivial⟩
  have g4r := wm_ready _ cap _ _ _ hwm (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
  have g4 := g4r.focus sS sS_inj a3 (by
    intro j
    fin_cases j
    · show a3 1 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_1]; rfl
    · show a3 12 = _
      rw [ha3, Function.update_self]; rfl
    · show a3 2 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_2]; rfl
    · show a3 3 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_3]; rfl
    all_goals
      (rw [ha3, Function.update_of_ne (by decide)]
       simp [ha2, FrontFill.side, tgtS, sS, wenc, role, FrontSize.st, FrontSize.d0, regTape_zero, hcap]))
  set a4 := install sS a3 (wenc cap (FrontSize.st o.isSome desc q (FrontSize.dF (sizeVerdict G q o)))).A with ha4
  refine ⟨a4, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 g4))) (by simp only [ssCost]; rw [hcap] at hn; omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha4, show (12 : Fin ST) = sS 1 from rfl, install_slot _ sS_inj]
    simp [wenc, role, FrontSize.st, FrontSize.dF]
  · rw [ha4, install_other _ _ _ _ (sS_ne 0 (by decide)), ha3, Function.update_of_ne (by decide),
      a2_other _ (by decide), a1_0]
  · rw [ha4, show (1 : Fin ST) = sS 0 from rfl, install_slot _ sS_inj]
    simp [wenc, role, FrontSize.st]
  · rw [ha4, show (2 : Fin ST) = sS 2 from rfl, install_slot _ sS_inj]
    simp [wenc, role, FrontSize.st]
  · rw [ha4, show (3 : Fin ST) = sS 3 from rfl, install_slot _ sS_inj]
    simp [wenc, role, FrontSize.st]

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSizeStage
