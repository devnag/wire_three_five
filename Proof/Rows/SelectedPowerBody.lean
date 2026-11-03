import Proof.Rows.SelectedPowerBank

/-! Consume the physically selected native child in the existing scaled mapper,
update the factor, and clear only the consumed native child buffer. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_SelectedPowerBank
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_HeaderRewind.clear

def equation {n : Nat} (g : ExactThresholdGate n):SupplierPipeline.LabelledEquation (Fin n):={weights:=g.weight,target:=g.target}

end
end PCJ45bee56da9f34d5a_SelectedPowerBody
