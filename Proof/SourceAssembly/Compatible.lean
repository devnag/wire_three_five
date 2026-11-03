import Proof.Assembly.ColdSource
import Proof.SourceAssembly.SourceRefill
import Proof.MachineModel.CacheRewind
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.OccurrenceRun
import Proof.Hierarchy.HierarchyFixedWord
import Proof.PCP.PCPPQueryNatural
import Proof.PCP.ProjectionDimensionPolynomialBounds

section

/-! One loose source-fixed preprocessing polynomial includes the capacity
factory, every source occurrence, allocation and all finalizer returns. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

def runtimeCoefficient:=DimensionPolynomial.coefficient (SourceEnvelope.degree a)
  (SourceEnvelope.coefficient a)+128*(SourceEnvelope.coefficient a+1)^2
def runtimeDegree:=2*SourceEnvelope.degree a+2

end NearCubicWires.ExtDecompositionBatch.Cold

end
