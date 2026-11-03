import Proof.Rows.RowsPartsFill
import Proof.Packets.PacketsMetaSeedCount
import Proof.Packets.PacketsMetaCutoffSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CostBound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.BlockPlatform NearCubicWires.ValidatorPolynomialDomination
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The fixed constants -/



/-! ## 2. The table term: `2^s` cells, each linear in `q`, `R`, `Bt` -/

/-! ## 3. The small term: C5 is linear in its arguments, each a fixed power of `smallSize` -/


/-! ## 4. Combining the three classes into `rowBudget` -/

end
end RowsConstruction.CostBound
