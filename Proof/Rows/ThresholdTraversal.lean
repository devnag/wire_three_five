import Proof.Rows.StreamCompare

/-! One actual THR traversal: native gates produce flags/count; selected TOP
children produce scaled coefficients; paid rewind joins the modular comparator.
Initial private masters, including the physically constructed canonical B,
remain the explicit input bank of this consumer. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_ThresholdTraversal
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_StreamPair
open PCJ45bee56da9f34d5a_StreamPairPorts
noncomputable section


variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 {cutoff :Nat} (prime :PrimeIndex cutoff) (o :Fin prime.val) (T L target w F U v C P :Nat)

def input:=PCJ45bee56da9f34d5a_StreamCompare.bank w
 (PCJ45bee56da9f34d5a_StreamPair.input a r four sel I x T L target prime.val w F U v o.val)

end
end PCJ45bee56da9f34d5a_ThresholdTraversal
