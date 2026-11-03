import Proof.Wire_3_5.Foundations.OutMachineCarGenBase

/-! # SB, part 17: X6's carrier pipeline for SB (counts only), at any capacity

SB (S4's words `4 … 7`) needs the carriers' atom counts (`carLen = 2·carCnt`, `s4Small2`) and their number, not the
tables. The pipeline (`CarPipe.carPipe`) at the keep list `keepLS` (the request, the two counts and
`1^{|carriers|}`) erases every other stream, the tables included, and runs at any capacity above its needs:

* `pipe_le_cap` (`pipeCost` within `(57600(D+1) + 10^6)·cap²`, `pipe_le` at a general capacity);
* **`carRunS`**: at a request of the family, at every capacity `≥ 2^{D}·(|fpIn|+1)^{D}` (`D = DtC`): the counts on
  `sCar k 5`, `1^{|carriers|}` on `s6`, the request kept, the erased streams and the log at `0^{(N+2)^D}`, heads,
  registers and the cell back at `0`/`false`.

Paper quantity of the main type: the carriers' atom counts (`|X_k|`, P3:3071-3086). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBCar
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarS NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

theorem pipe_le_cap (cap Dt N n : ℕ) (hDt : 1 ≤ Dt) (codes : List ℕ) {n' : ℕ} (carriers : List (Stars.Carrier n'))
    (hT1 : m1Cost (c1Of n) n ≤ (N + 2) ^ Dt)
    (hT2 : Lof n + Out.CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers ≤ (N + 2) ^ Dt) (hTC : (N + 2) ^ Dt ≤ cap) :
    pipeCost cap Dt N n codes carriers ≤ (57600 * (Dt + 1) + 10 ^ 6) * cap ^ 2 := by
  have hN2 : N + 2 ≤ (N + 2) ^ Dt := Nat.le_self_pow (by omega) _
  have hsq := sq_le cap cap (by omega)
  have hCC : cap ≤ cap ^ 2 := Nat.le_self_pow (by norm_num) _
  have hmk : mkTCost cap Dt N ≤ (Dt + 1) * (4 * PrimAsm.UnaryPow.sq cap) + 27 * N + 12 := by unfold mkTCost; omega
  have hmk2 : (Dt + 1) * (4 * PrimAsm.UnaryPow.sq cap) ≤ (Dt + 1) * (28800 * cap ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hr : (Dt + 1) * (28800 * cap ^ 2) = 28800 * ((Dt + 1) * cap ^ 2) := by ring
  have hr2 : (57600 * (Dt + 1) + 10 ^ 6) * cap ^ 2 = 57600 * ((Dt + 1) * cap ^ 2) + 10 ^ 6 * cap ^ 2 := by ring
  rw [hr2]
  unfold pipeCost s1Cost s3Cost
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBCar
