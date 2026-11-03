import Proof.Assembly.RowProduction
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryRowLookupTapes

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Plan
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

def clearInput {m : Nat} (K logCapacity : Nat) (A : Fin m → List Bool) :
    Fin (m+1+1) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate K true))
    (fun _ : Fin 1 => List.replicate logCapacity false)

def clearOutput (m K logCapacity : Nat) : Fin (m+1+1) → List Bool :=
  clearInput K logCapacity (fun _ : Fin m => List.replicate K false)

end
end PCJ45bee56da9f34d5a_Plan
