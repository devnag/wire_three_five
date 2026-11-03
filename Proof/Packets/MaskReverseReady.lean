import Proof.Rows.MaskSeek
import Proof.Packets.PhysicalParityRestore

/-! Fixed-width bank reversal starts and ends at the bank's entry cursor.
The appended reversed bank is physically positioned for immediate consumption. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverseReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def raw := Composition.machine MaskSeek.machine MaskReverse.machine
noncomputable def machine := CursorRestore.machine raw 2


end PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverseReady
