import Proof.Packets.SubstitutionCallFinish

/-! A fully executed reusable substitution call. Its input polynomial is
resident in the right operand; the source copy and loop drivers are physically
created, all cursor motion is paid, and all nine private tapes are erased. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def prepare := Composition.machine machine (Composition.machine (moveDrivers .right) seek)
noncomputable def execute := Composition.machine prepare (Composition.machine SubstitutionOuter.machine finish)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
