import Proof.Packets.PacketsXVectorPhaseChange
import Proof.Packets.PacketsXVectorDepthMaster
import Proof.Packets.PacketsXVectorBankInitialize

/-! Closed physical initialization for the bottom-up controller. Source
population/depth are retained; all loop drivers and both vector banks are
constructed by execution before the first level. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] phaseChange depthMaster initializeDrivers populationMaster initializeVectors

def initializeController := Composition.machine phaseChange (Composition.machine depthMaster
  (Composition.machine initializeDrivers (Composition.machine populationMaster initializeVectors)))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
