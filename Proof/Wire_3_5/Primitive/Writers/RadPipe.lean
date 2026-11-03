import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Wire_3_5.Primitive.Writers.PopPipe
import Proof.Wire_3_5.Lists.ListMachineRowRadixContract

/-! # The RADIX pipe: C2's RADIX row machine docked on the THR unit's cell (row:radix)

From THR's `Joins.RadReady` (the framed record `frame r.record` on stream `3`, the output `out ++ [false]` at
`|out|`, the RADIX flag, every scratch stream empty, `r.Pre`), C2's RADIX row machine `radRowM (negFam F35)` on the
POP row's streams `tmapQ` (record `3`, output `1`, scratch `30 … 76`) prints the row's reference expression
`radRefC r.D r.digs r.p r.b0 r.s` on the output; the output head then steps back before the closing `false`.

* `radRowDM`, **`radRowStage`**; `radPipeM`, `radPipeBound` (`RadReq.bound + 2`, C2's `(M+1)^{2τ}·128·(|record|+1)²`);
* **`radPipe_ready`**: the pipe's run from `RadReady` (output `out ++ body ++ [false]`, head `|out ++ body|`; the
  request, the counter and the data kept).

Paper quantity of the main type: the RADIX row's printed reference (`WriterIface.refOf (.rad r)`, row:radix
P3:2585-2623, whose value is `[Σ_d b_0^d(t_d^+ − t_d^−) ≡ s (mod p)]`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.RadPipe
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

section Rad
variable (cap : ℕ) {x : ℕ}

variable (x) in
/-- The RADIX row stage's machine: C2's RADIX row machine on the streams `tmapQ`. -/
noncomputable def radRowDM := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tmapQ x j)) (radRowM (negFam F35))

theorem tmapQ_ne3 (k : Fin 161) (hk : k.val = 0 ∨ k.val = 2 ∨ k.val = 113) (j : Fin (IPL (negFam F35).t + 1)) :
    tmapQ x j ≠ sk x k := by
  intro h
  have hv := congrArg Fin.val h
  have e : (tmapQ x j).val = (portP (Fin.cast IPL1 j)).val := rfl
  rw [e, portP_val, Fin.val_cast, sk_val] at hv
  have := j.isLt
  have h47 := IPL_val
  split_ifs at hv <;> omega

variable (x) in
/-- **The RADIX pipe**: the row stage, then the output head back. -/
noncomputable def radPipeM := Composition.machine (radRowDM x) (bwdM x)

end Rad

end NearCubicWires.WireExponent3_5.PrimAsm.RadPipe
