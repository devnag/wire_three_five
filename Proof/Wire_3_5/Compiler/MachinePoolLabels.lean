import Proof.Wire_3_5.Compiler.MachinePoolUcopy

/-! # C3a, the pool builder: the label word of a population (word (3))

Paper: the common pool over all star rows (P3:1655-1664) with the numbering: corner `k` of star row
`rowIdx` for carrier gate `gi` is atom `(4·rowIdx + k)·G + gi`. C2 prints a population's factors over these global
atoms, reading the label word `labelWord (labsOf G rowIdx gis)`: four corner labels per gate occurrence, each a unary
code. The machine computes the labels from `G`, `rowIdx` and the occurrences `gis`, all in unary:
* phase 1: `4·rowIdx` ones (four copies of `rowIdx`);
* phase 2: the base `4·rowIdx·G` ones (one copy of `G` per one of phase 1);
* phase 3, per occurrence `gi`: load `gi`, then for `k = 0, 1, 2, 3` write the base, `k` copies of `G`, `gi`, and `0`;
* then the closing `0`.

The paper quantity of the main theorem is word (3): **`labels_run`** writes `labelWord (labsOf G rowIdx gis)`. Main
declarations: `p1R`, `p2R`, `giBody`, `labelsM`, **`labels_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)


/-! ## Phase 1: `4·rowIdx` ones (tapes: 0 rowIdx, 1 the result, 2 a log) -/

/-! ## Phase 2: the base `4·rowIdx·G` ones (tapes: 0 phase 1's ones, 1 `G`, 2 the base, 3 a log) -/


/-! ## Phase 3: one occurrence's four labels (tapes: 0 the occurrences, 1 the occurrence register, 2 the output,
3 the base, 4 `G`, 5 a log, 6 the register's log) -/



section Corner

end Corner



section Corners


end Corners

/-! ## The label word -/


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
