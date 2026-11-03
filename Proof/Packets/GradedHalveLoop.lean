import Proof.Packets.GradedHalveRound

/-! Physical iteration of the reusable ceiling-halver with the actual unary
quotient driver. Its zero case executes the same fixed Repeat machine. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine := RepeatMachine.machine GradedHalveRound.round (fun _ _=>true)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveLoop
