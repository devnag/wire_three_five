import Proof.MachineModel.TopDownPaidReusableReserves
import Proof.MachineModel.TopDownPaidFamilyConsumers
import Proof.MachineModel.ClosureBinaryHeaderCapacity
import Proof.CaseAnalysis.RawRowsLoad
import Proof.CaseAnalysis.RowsUniversalResources
import Proof.MachineModel.ClosureBinaryPreparedCost
import Proof.MachineModel.P1ClosureCompactCost
import Proof.MachineModel.ClosureBinaryRowCost

/-! One explicit reserve for every actual binary request in a family. Existing
header production and original-degree driver estimates discharge the capacities.
These arithmetic facts leave the physical source/template production visible. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidBinaryReserves
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler SourceInterfaces
open RepairSource CloseoutFinal P1TopDownPaidReusable P1TopDownPaidReusableReserves
attribute [local irreducible] BinaryPool.pool CompactBounds.radix

def headerCapacity (q s c e : Nat) : Nat :=
  (2^230*(c+5)^88)*(q+1)^((e+1)*88)*2^(s/8)+1
noncomputable def driverCapacity (printer : WilliamsAlgorithm) (q s c e : Nat) : Nat :=
  64*(headerCapacity q s c e+1)+2^21*(c+4)^3*(q+1)^((e+2)*3)*2^(s/32)+
    CompactCost.tableCoefficient printer c*
      (2^s*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer))

end NearCubicWires.P1TopDownPaidBinaryReserves
