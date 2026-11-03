import Proof.Assembly.ColdSource
import Proof.SourceAssembly.PoolDonorCompatible
import Proof.PCP.ProjectionDimensionPolynomialBounds
import Proof.Circuits.DecompositionCountPosition

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Cold's paid bound (copy of `ColdCompatible`'s `ColdBudget`, renamed) -/

namespace RowsConstruction.I2c.ColdBudget
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtDecompositionBatch.Cold
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairOrdinary.DecompositionSource NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open NearCubicWires.RepairSource.ProjectionNormalization


end RowsConstruction.I2c.ColdBudget

/-! ## 2. The paired pool writer followed by Cold (copy of `PoolColdCompatible`, renamed) -/

namespace RowsConstruction.I2c.PoolCold
open NearCubicWires LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairSource SupplierPipeline RepairRepresentation VerifierDecoding P1Closure
open scoped BigOperators
attribute [local irreducible] PoolEntryOccurrence.machine Cold.machine



end RowsConstruction.I2c.PoolCold

/-! ## 3. The cache port and the rewound domain port (copy of `SourceCache.ready_run`, renamed) -/

namespace RowsConstruction.I2c.PoolReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open RowsConstruction.I2c
noncomputable section


end
end RowsConstruction.I2c.PoolReady
