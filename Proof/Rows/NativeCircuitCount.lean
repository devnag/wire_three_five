import Proof.Rows.NativeGateLoop
import Proof.Rows.TopArity

/-! The original circuit's actual first nat header produces the bottom-loop
count. Reader scratch and its capacity/log reuse the existing gate bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopArity.machine

def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (source fields framed out count : List Bool) (Q : Nat) : Fin 124→List Bool :=
 Fin.addCases (m:=123) (n:=1) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_CountedGateCell.bank
    (PCJ45bee56da9f34d5a_FramedGateBank.bank live x w H R U source fields framed out) Q) (fun _=>count)

end
end PCJ45bee56da9f34d5a_NativeCircuitCount
