import Proof.Packets.WalkSeedSlice

/-! Actual seed slicing with paid restoration of every cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open WalkSeedSlice

noncomputable def machine:=MaskedReset.machine WalkSeedSlice.machine (fun _=>true)

end Theorem25Completion.WalkSeedReady
