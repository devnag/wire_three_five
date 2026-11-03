import Proof.Assembly.BankFamilyBankInitializer

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
open RepairRepresentation SourceInterfaces
open PCJ1fef9807c6954e94_Native
namespace PCJ34388a2fbfa9464b_
attribute [local irreducible] P1TopDownPaidPayload.tapes

noncomputable def machine (a : WilliamsAlgorithm) : Machine (PCJ515eaa990d75455b_FamilyInit.initTapes a) 39 := by
 unfold PCJ515eaa990d75455b_FamilyInit.initTapes
 exact Bank.machine (P1TopDownPaidPayload.tapes a)

attribute [local irreducible] Step Bank.machine

end PCJ34388a2fbfa9464b_
