import Proof.Packets.ParityFilterLoop
import Proof.Packets.ParityFilterBody
import Proof.Packets.PhysicalParityRestore

/-! The coefficient filter returns its output cursor and freshly produced
unary count cursor to the serializer ABI by two paid, erased movement logs. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def readyMachine := CursorRestore.machine (CursorRestore.machine machine 7) 8

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
