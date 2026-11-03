import Proof.Rows.NativeScaleWeights

/-! A selected native child is physically mapped to scaled residues in native
weight order, followed by its negative target. The count driver is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleEquation
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey
noncomputable section

def weights {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)):=List.ofFn eq.weights
def result (a p w : Nat) {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)):=
  FinalPrimeModular.blocks (PCJ45bee56da9f34d5a_NativeScaleWeights.words a p w (weights eq)) 0 n++
    frame (binary w ((a*FinalPrimeReduce.intResidue p (-eq.target))%p))
def budget (n F w U : Nat) (target : Int):=PCJ45bee56da9f34d5a_NativeScaleWeights.budget n F w U+1+PCJ45bee56da9f34d5a_NativeScaleRun.budget true target w F U

end
end PCJ45bee56da9f34d5a_NativeScaleEquation
