import Proof.Packets.SubstitutionBit
import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.PacketVector

/-! The complete descending literal-bit product loop. Every iteration is the
actual decrement/read/lookup/multiply worker, driven by a resident unary width.
The step guards are the concrete reserve inequalities, not execution advice. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding


noncomputable def machine := RepeatMachine.machine SubstitutionBit.machine (fun _ _=>true)



end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScan
