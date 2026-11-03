import CheckedPCPP.WMXReady
import Codec.Emit
import Codec.Unframe
import Proof.MachineModel.OrdinaryOracleComposeClock
import Proof.Wire_3_5.Compiler.MachineEmitPad

/-!
# W3dl, piece 1, part A: the guard writer (`guardP`), the natWord copier (`copyK`), the tally (`tallyP`)

All on exact states (the ideal-form transfer is at the end, CtrCall.lean).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

/-! ## Two ones -/

/-! ## The guard from the input frame -/

end NearCubicGates.Close.WorkerArith
