import Proof.Wire_3_5.Primitive.Writers.ThrSet4

/-! # c4 THR block, the THR setup on the big bank, run (`setupT_run`)

The THR setup's exit bank: on the layout (the first tapes) C4Cap.setup_run2's exit list (the request, the batch, a
blank port `2`, the thirty-nine words, the modulus words, the big unary words, the compiler request's fields, the log, the
pads), the marked hash bits on `hbT`, the bank blank from the finisher's region up.

Paper quantities of the main type: the loop's entry words and the finisher's inputs on their tapes (P3:3011-3016),
with the THR call's numbers and hash bits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
