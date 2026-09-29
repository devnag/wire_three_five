import Proof.CaseAnalysis.FinalWorkerChain

/-! # W1 -- the AND-four call stream is folded by an actual machine run

Paper C.10.1 (paper.tex 4103):

> estimates `mu = E_{i,u} F_i(u)` **by expanding it into AND-four supplier
> calls**, and accepts a branch only if `mu~ >= theta_acc := (c_p+s_p)/2`.

`RepairCloseoutFinalC10WorkerChain` proved the identity half: the exact signed
rational fold of the call stream has value `polynomial.estimatedMean supplier`.
This module supplies the physical half from the corpus's own cold fold
(`CompetitorSumEntry.uniform_cold_sum_run`, GREEN): **one real execution**,
from all heads at zero with every work tape blank, consumes the call stream and
leaves the numerator pair and denominator of `mu~` in the accumulator fields.

The two halves meet in `coldFold_estimatedMean`, whose conclusion names both
the receipt and the paper's estimated mean.  That is the C.10.1 sentence as a
machine fact: a run exists, and what it computed is `mu~`.

What remains of `EstimatorBody` after this module is exactly two stages: the
stage that PRODUCES the call stream at each PCPP clause address, and the stage
that EMITS `Stream.recordWord` from the stored accumulator fields.  The fold
between them is no longer an obligation.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 One supplier call per monomial -/

/-! ## §2 The fold, as one real execution -/

/-- The scalar width the cold fold runs at: the corpus's uniform prefix width
for a stream of `n` records each valid at `recordWidth`. -/
def foldWidth (recordWidth : ℕ) (entries : List Entry) : ℕ :=
  CompetitorSumWidth.width (contributions entries).length recordWidth

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
