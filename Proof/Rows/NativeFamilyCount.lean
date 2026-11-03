import Proof.Rows.CircuitCountAdvance
import Proof.Rows.NativeFlags

/-! Dock the actual fifth-header count producer into the final circuit-loop
bank, preserving its advancing native source and the gate evaluator masters. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFamilyCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section

def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat) (source out count : List Bool):Fin 128→List Bool:=
 Fin.addCases (m:=127) (n:=1) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_CircuitFlagBank.bank live x B source [] [] out (List.replicate (U B q (B+1)) false) Q) (fun _=>count)

end
end PCJ45bee56da9f34d5a_NativeFamilyCount
