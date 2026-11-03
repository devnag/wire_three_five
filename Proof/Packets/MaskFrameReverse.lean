import Proof.Packets.MaskFrameLoop
import Proof.Packets.MaskProductOuter

/-! Reverse-order framing without a supplied reversed bank or extra data tape. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def backSlots : Fin 3→Fin 5 := ![0,2,1]
noncomputable def reverseBody := Composition.machine (RecoveryFocus.machine backSlots MaskBack.body)
  (Composition.machine machine (RecoveryFocus.machine backSlots MaskBack.body))

noncomputable def reverseLoop := RepeatMachine.machine reverseBody (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
