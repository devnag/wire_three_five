import Proof.CaseAnalysis.FinalWorkerJoin

/-! # W1 -- one AND-four supplier call, emitted as one record word

Paper C.10.1 (paper.tex 4103):

> estimates `mu = E_{i,u} F_i(u)` **by expanding it into AND-four supplier
> calls**.

Paper C.10 (paper.tex 4098-4110):

> **All expressions have degree at most four in the guessed sums.** ... **no
> parity-support enumeration occurs.**

`CloseoutRowsEstimatorCoefficients.CloseoutRowsEstimatorCoefficients.Append.record_run` (GREEN) is the corpus's
record emitter: from the six scalar operands of one call -- the monomial's
rational coefficient as a signed pair with its denominator, and the supplier's
`count / denominator` answer -- one real execution writes
`Stream.recordWord` on its output tape, at a cost that depends only on the
scalar width.  This module uses it twice.

* `call_record_run`: **one call, one record.**  With a `Calls` hypothesis the
  emitted word is `Stream.entryWord`, the very record the multiply stage of
  `RepairCloseoutFinalC10WorkerJoin` reads, and the emitted operands are the
  monomial's coefficient and the supplier's answer to its at-most-four factor
  list.  Nothing about `BitInput` is enumerated: the `u`-average is the
  supplier's business, inside `conjunctionProbability`.

* `estimate_record_run`: **the answer, as the encoder writes it.**  Applied to
  the fold's accumulator at `count = denominator = 1`, the same emitter
  produces `Stream.recordWord width estimate 1 1` -- literally the right-hand
  side of `Realizes.hencoded` -- and the accompanying identity says that the
  estimate so encoded has value `polynomial.estimatedMean supplier`, which is
  `Realizes.hvaluesum`.

With this module, the only remaining obligation inside `EstimatorBody` is the
stage that PRODUCES the per-call operands at each PCPP clause address (the
supplier's own `count`), and the tape-level docking of the four stages into one
bank behind P4's length gate.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit
