import Proof.Wire_3_5.Primitive.Writers.SBLayBase

/-! # SB, part (3b): SB's machine run and exit state

* `Pof` (the call's star parameters), `sbCost`;
* **`sb_run`**: at a request of the family, from the input frame (every other stream blank, heads, registers `0`, the
  cell `false`), at every capacity `cap ≥ sbNeed`, `sbMach` leaves `SBExit` on `sOutB` (S4's words `4 … 7` in the
  registers' shapes), the input kept, every other stream of length `≤ cap`, heads and registers `0`, within `sbCost`.

Paper quantities of the main type: S4's words `4 … 7` at a star call (`s4Core2`, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarS
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums NearCubicWires.WireExponent3_5.PrimAsm.SBTypes
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.DockW

theorem pow_two_mul (N D : ℕ) : (N + 2) ^ D ≤ 2 ^ D * (N + 1) ^ D := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) D

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
