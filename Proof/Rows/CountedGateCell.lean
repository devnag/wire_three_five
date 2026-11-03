import Proof.Rows.FramedGateRun
import Proof.Rows.MinimumMaskCell

/-! Each actual original-gate verdict also emits one unit of the final
comparator dimension. The count cursor stays at its writable end. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CountedGateCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank PCJ45bee56da9f34d5a_UniformMinimumBounds
open scoped BigOperators
noncomputable section

def bank (a : Fin 122→List Bool) (Q : Nat) : Fin 123→List Bool := Fin.addCases (m:=122) (n:=1) (motive:=fun _=>List Bool) a (fun _ : Fin 1=>CompareMachine.word Q)

def cost (B q w : Nat) :=131072*(B+q+w+1)^2+2

end
end PCJ45bee56da9f34d5a_CountedGateCell
