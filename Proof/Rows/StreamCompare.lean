import Proof.Rows.StreamPairPorts
import Proof.CaseAnalysis.RowsOriginalClauseLoop
import Proof.Rows.FinalNativeResidueCallback
import Proof.Rows.OffsetEmitter
import Proof.Rows.ThresholdData

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

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 {cutoff :Nat} (prime :PrimeIndex cutoff) (o :Fin prime.val) (T L target w F U v :Nat)

def bits:=occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x
def count:=(PCJ45bee56da9f34d5a_ExpandedThresholdStream.terms a r sel (bits r I x)).length+1

end
end PCJ45bee56da9f34d5a_StreamCompare
