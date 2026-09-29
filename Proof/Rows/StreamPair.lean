import Proof.Rows.CoefficientRun
import Proof.Rows.NativeFamilyFlags

/-! The actual native flag/count traversal and selected TOP coefficient
traversal run on one fixed pair of banks. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamPair
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_UniformMinimumBounds
open PCJ45bee56da9f34d5a_NativeFlagsMeaning (circuits)
noncomputable section



variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)

def native (L target :Nat):=PCJ45bee56da9f34d5a_NativeFamilyFlags.source 1 L target (circuits r)
def data:=PCJ45bee56da9f34d5a_ThresholdData.data a r four sel
def radix:=PCJ45bee56da9f34d5a_ThresholdData.base a r four sel

def flagStart (T L target :Nat):Fin 128→List Bool:=
 PCJ45bee56da9f34d5a_NativeFamilyCount.bank I x T 0 (native r L target) [] (List.replicate (U T r.q (T+1)) false)

def input (T L target p w F U v o :Nat):Fin 250→List Bool:=
 Fin.addCases (m:=128) (n:=122) (motive:=fun _=>List Bool) (flagStart r I x T L target)
  (PCJ45bee56da9f34d5a_CoefficientRun.bank (data a r four sel) 1 (radix a r four sel) p w F U v o [])

end
end PCJ45bee56da9f34d5a_StreamPair
