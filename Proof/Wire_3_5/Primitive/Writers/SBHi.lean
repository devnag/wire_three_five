import Proof.Wire_3_5.Primitive.Writers.SBNumsF

/-! # SB, part 19: the small-number phases leave registers `97 … 111` unchanged

The field phase (S4's words `4`, `5`) runs on registers `96 … 111` with `96 = ℓ` and the rest `0`; the phases of
`SBNums` write only registers below `97`:

* `a_hi`, `b1_hi`, `b2a_hi`, `b2b_hi`, `b2c_hi`, `c1_hi`, `c2_hi`, `c3_hi`.

Paper quantity: none (register bookkeeping). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.WireExponent3_5.PrimAsm.CapNum

section Run
variable {ns : ℕ}

theorem a_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (aOut σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [aOut, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem b1_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (b1Out σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [b1Out, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem b2a_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (b2aOut σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [b2aOut, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem b2b_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (b2bOut σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [b2bOut, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem b2c_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (b2cOut σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [b2cOut, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem c1_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (c1Out σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [c1Out, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem c2_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (c2Out σ P h0 h1 Cδ C m fe).val r = σ.val r := by
  simp only [c2Out, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

theorem c3_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (c0 c1 : ℕ) (σ : WState ns NRB) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (c3Out σ P h0 h1 Cδ C m fe c0 c1).val r = σ.val r := by
  simp only [c3Out, StarNums.starOut, WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.SBNums
