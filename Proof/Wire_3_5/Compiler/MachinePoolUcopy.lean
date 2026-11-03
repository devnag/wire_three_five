import Proof.Wire_3_5.Compiler.MachinePoolRun

/-! # C3a, the pool builder: unary copies for the label words

Paper: the pool numbering fixed (from P3:1655-1664's "common pool over all `2^k` rows"): atom
`(4·rowIdx + k)·G + gi`. C2 reads a population's labels as unary codes (`labelWord`); a unary number is written
by copying unary blocks. `ucopyM` copies the ones of a unary source onto an output cursor.

The paper quantity of the main theorem is the copied unary block: **`ucopy_run`**, and with the source head returned,
**`ucopyStep`**. Main declarations: `ucopyM`, `ucopy_timed`, `ucopyR`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- Copy ones: while the source reads `1`, write `1` on the output and move both right; halt on `0`. -/
def ucopyM : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then ⟨0, ![none, some true], ![.right, .right]⟩ else ⟨1, fun _ => none, fun _ => .stay⟩)
    else none

/-- A unary copy with the source head returned to `0` (log on tape 2). -/
noncomputable def ucopyR := MaskedReset.machine ucopyM ![true, false]


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
