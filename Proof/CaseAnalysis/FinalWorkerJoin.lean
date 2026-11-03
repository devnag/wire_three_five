import Proof.CaseAnalysis.FinalWorkerFold

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The scalar width at which the multiply stage and the fold agree: the fold's
own uniform prefix width for `entries.length` records of scalar width
`CompetitorRationalDecision.width recordWidth`. -/
def joinWidth (recordWidth : ℕ) (entries : List Entry) : ℕ :=
  foldWidth (CompetitorRationalDecision.width recordWidth) entries

theorem contributions_length (entries : List Entry) :
    (contributions entries).length = entries.length := by
  rw [contributions, List.length_map]

/-- The multiply stage's scalar width fits inside the join width. -/
theorem width_le_joinWidth (recordWidth : ℕ) (entries : List Entry) :
    CompetitorRationalDecision.width recordWidth ≤ joinWidth recordWidth entries := by
  unfold joinWidth foldWidth CompetitorSumWidth.width
  nlinarith [Nat.zero_le (contributions entries).length,
    Nat.zero_le (CompetitorRationalDecision.width recordWidth)]

/-- One call per record fits inside the join width. -/
theorem length_le_joinWidth (recordWidth : ℕ) (entries : List Entry) :
    entries.length ≤ joinWidth recordWidth entries := by
  unfold joinWidth foldWidth CompetitorSumWidth.width
  rw [contributions_length]
  nlinarith [Nat.zero_le entries.length,
    Nat.zero_le (CompetitorRationalDecision.width recordWidth)]

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
