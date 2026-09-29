import Proof.Rows.NativeCircuitFlags

/-! Resident original circuit stream plus one reusable frame buffer. Unwrapping
reuses the copy log; the full resident stream never enters the gate reserve. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section

def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B : Nat)
 (source raw framed out count : List Bool) (Q : Nat) : Fin 127→List Bool :=
 Fin.addCases (m:=124) (n:=3) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_NativeCircuitCount.bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1))
   (ZeroPadding.pad (U B q (B+1)) raw) (List.replicate (H B q (B+1)) false)
   (List.replicate (H B q (B+1)) false) out count Q)
  ![source,ZeroPadding.pad (U B q (B+1)) framed,List.replicate (U B q (B+1)) false]

def caps (U : Nat) (i : Fin 124) :=if i=114 then U else 0

end
end PCJ45bee56da9f34d5a_CircuitFlagBank
