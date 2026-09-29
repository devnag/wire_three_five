import Proof.Rows.StreamPairPorts

/-! Dock the exact modular comparator onto the produced, paid-rewound
native flag/count and selected coefficient streams. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamCompare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_StreamPair
open PCJ45bee56da9f34d5a_StreamPairPorts
noncomputable section

def registers (w :Nat):Fin 4→List Bool:=![frame (binary w 0),frame (binary w 0),[false],[false]]
def bank (w :Nat) (A :Fin 250→List Bool):Fin 254→List Bool:=
 Fin.addCases (m:=250) (n:=4) (motive:=fun _=>List Bool) A (registers w)


end
end PCJ45bee56da9f34d5a_StreamCompare
