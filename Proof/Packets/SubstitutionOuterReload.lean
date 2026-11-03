import Proof.Packets.SubstitutionOuterData
import Proof.Packets.PhysicalIndexReload

/-! Paid restoration of the literal index between monomials. The resident
common-width template is copied only after lowering the actual index head. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def reload := PhysicalIndexReload.machine (31 : Fin 43) 24 35

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
