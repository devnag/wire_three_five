import Proof.Wire_3_5.Foundations.OutMachineJoin

/-! # Writer combinators, part 2: `join`, `reindex`, `congrWs`, `sub`

* the joint layout of two writers `W`, `W'`: streams `e1` (`W`'s), `e2` (`W'`'s), `W'`'s input read on `W`'s
  (`f2`); registers `g1`, `g2`; the outputs `sOutJ` (`W`'s, then `W'`'s);
* **`join_run`**: `W` runs on its block, the cell is reset, `W'` runs on its block reading the kept input;
* **`CoreWordsMJ.join`**, **`CoreWordsMJ.reindex`**, **`CoreWordsMJ.congrWs`**, **`CoreWordsMJ.sub`**.

Paper quantity of the main type: the front's words at a request (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Join
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW

section JoinLay
variable {l : Literals} {m m' : ℕ}
 
 
 

theorem pow_mono_add (N x y : ℕ) : (N + 1) ^ x ≤ (N + 1) ^ (x + y) :=
  Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.le_add_right _ _)

theorem pow_mono_add' (N x y : ℕ) : (N + 1) ^ y ≤ (N + 1) ^ (x + y) :=
  Nat.pow_le_pow_right (Nat.succ_pos N) (Nat.le_add_left _ _)

theorem bnd_le (C C' P Q x : ℕ) (hP : P ≤ Q) (hx : x ≤ C * P) : x ≤ (C + C' + 4) * Q := by
  have h1 := Nat.mul_le_mul_left C hP
  have e : (C + C' + 4) * Q = C * Q + (C' * Q + 4 * Q) := by ring
  rw [e]
  omega

theorem bnd_le' (C C' P' Q x : ℕ) (hP' : P' ≤ Q) (hx : x ≤ C' * P') : x ≤ (C + C' + 4) * Q := by
  have h1 := Nat.mul_le_mul_left C' hP'
  have e : (C + C' + 4) * Q = C * Q + (C' * Q + 4 * Q) := by ring
  rw [e]
  omega

theorem bnd_sum (C C' P P' Q n1 n2 : ℕ) (hP : P ≤ Q) (hP' : P' ≤ Q) (hQ : 1 ≤ Q) (h1 : n1 ≤ C * P)
    (h2 : n2 ≤ C' * P') : n1 + 1 + (1 + 1 + n2) ≤ (C + C' + 4) * Q := by
  have a1 := Nat.mul_le_mul_left C hP
  have a2 := Nat.mul_le_mul_left C' hP'
  have e : (C + C' + 4) * Q = C * Q + (C' * Q + 4 * Q) := by ring
  rw [e]
  omega

end JoinLay

end NearCubicWires.WireExponent3_5.FinalPass.Out.Join

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Out.Join

end NearCubicWires.WireExponent3_5.FinalPass.Finish
