import Proof.CaseAnalysis.FinalCacheRewind
import Proof.MachineModel.Layout

/-! Original input, witness and mode bytes belong to the same original-input
cold run. One recording rewind resets every head, and focus retains the exact
ambient complement. No prepared bank or second source execution is assumed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdOriginalFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch SourceInterfaces
open RepairSource RepairRepresentation ProjectionNormalization CloseoutWitness
open RecoveryRootRound CloseoutFinalC10ColdCacheAtAdmission
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdOriginalFrame
