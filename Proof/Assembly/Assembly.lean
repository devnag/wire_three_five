import Proof.Assembly.Front

/-! The checked physical join: initialize the resident descriptor bank,
preserve the denominator outside the focus, and retain the exact fuel sum. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ2bf639ce0c7c470f_Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit

attribute [local irreducible] CompetitorCrossScheduler.producer
  P1TopDownPaidReusable.machine P1TopDownPaidReloadCore.rawMachine
  P1TopDownPaidReusableBody.machine


end PCJ2bf639ce0c7c470f_Assembly
