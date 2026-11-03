import Proof.Packets.PacketsXVectorDriverBoot
import Proof.Packets.UnaryHalf

/-! The provider's literal population is twice the original population.
A paid unary halving generates the actual vector population master before
constructing the child and parent drivers. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def populationSlots : Fin 3→Fin 299 := ![184,281,282]
def populationMachine := RecoveryFocus.machine populationSlots UnaryHalf.returned
def initializeDrivers := Composition.machine populationMachine bootDrivers

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
