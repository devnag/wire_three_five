import Proof.MachineModel.Runs
import Proof.MachineModel.UWalkUnary
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Packets.PacketsXLiteralPairCache
import Proof.Packets.PacketsXCycleLiteralCacheBounded
import Proof.Packets.PhysicalBoundedLeftRewind

/-! Complete cold reflected singleton cache: allocate all scratch and loop
drivers, construct codes in the exact descending order, then physically
return the emitted cache cursor to zero. Only actual raw R and the actual
unary tag/count templates are supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Theorem25Completion Theorem25Completion.CycleLiteralPairCost Completion
noncomputable section

def slots : Fin 2→Fin 68 := ![62,2]
def loop := TapeEmbedding.machine 6 LiteralPairCache.machine
def rewind := RecoveryFocus.machine slots PhysicalBoundedLeftRewind.machine


end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheCold
