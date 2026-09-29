import Proof.MachineModel.FrameCopy
import Proof.MachineModel.OrdinaryWilliamsInputHeader
import Proof.MachineModel.Runs

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsGlue.NatSum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue

/-! ## The machine -/

/-! ## Tape shapes -/


/-! ## The source: a frame read two cells per logical bit -/

/-! ## One transition each -/

section Steps

end Steps

/-! ## The loops -/

section Loops

end Loops

section WLoops

end WLoops

/-! ## One bit, then all bits -/

macro "cfg_eq" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (congr 1 <;> omega)))

/-! ## One natWord, then the list -/

/-! ## The whole run -/

end NearCubicWires.PacketsGlue.NatSum

