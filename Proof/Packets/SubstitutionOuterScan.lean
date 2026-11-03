import Proof.Packets.SubstitutionOuterData

/-! The executed descending product loop docked into the outer sum arena. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding





noncomputable def scanMachine := RecoveryFocus.machine (Fin.castAdd 4) SubstitutionScan.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
