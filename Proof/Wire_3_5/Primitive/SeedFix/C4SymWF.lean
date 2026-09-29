import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE

/-! # C4 SYM stage, part 6: the SYM stage from the setup at capacity `2^m` (the cap re-type's consumer dock)

P3:3011-3016 (the setup before the loop), P3:2929-2941, 2994-3000 (`ℓ`, `Q` held by the numbers machine at capacity
`2^m`), P3:3034-3038 (the decisions), P3:2932-2937 (the samples). `C4Cap.setup_run2`'s exit bank is a `SymBank` bank once
the numbers program's words are `symClean` at the call's numbers (`bigS_spec`) and the numbers are linked to the child
family's parameters; with `symLay_run` the whole SYM stage runs:

* `symMachine` (the stage's machine: `setupM2 ; loop ; sample expansion`), **`symSetup_stage`**.

Paper quantity of the main type: the stage's output `sampleWord kh (seedPairs P s)`, the fixed seed's samples. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
