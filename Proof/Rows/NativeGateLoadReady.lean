import Proof.Rows.CellGatePalette
import Proof.Rows.HeaderRewind
import Proof.Rows.TopChildCursor
import Proof.SourceAssembly.PoolDonorCompatible

/-! Actual native gate frame to signed fields, with paid scratch reuse. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeGateLoadReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] PoolEntryLoad.machine

def slots : Fin 8→Fin 11 := ![1,2,3,4,7,8,9,10]
def load := TapeEmbedding.machine 2 PoolEntryLoad.machine
def clear := RecoveryFocus.machine slots (PCJ45bee56da9f34d5a_HeaderRewind.clear 6)
def machine := Composition.machine load clear

end
end PCJ45bee56da9f34d5a_NativeGateLoadReady
