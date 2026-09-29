import Proof.Assembly.FamilyInit

/-! Exact physical prefix/initializer junction. Native production is stated
as an actual Step from the nine input words, with a complete PrefixReady bank.
The bridge obligation proves the physical join and retains all semantic and
resource fields of the existing full generator contract. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace PCJ9a78bdaedf5d4482_Front
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJf990607ff5714139_Generator
open P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

end PCJ9a78bdaedf5d4482_Front
