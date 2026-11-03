import Proof.CaseAnalysis.RawRowsThresholdAccuracy
import Proof.Rows.FinalPrimeResidueWord
import Proof.Rows.FinalPrimeThresholdRow
import Proof.Rows.FinalPrimeModularSum

/-! # The per-coefficient modular reduction loop

`FinalPrimeThresholdRow.threshold_row_run` emits the threshold row's accept bit
from a stream of summand words `w`, but it *assumes* four facts about that
stream: each word has the prime's width, each word is already reduced below the
prime, and the words are congruent to the equation's weights (and to `-target`
in the last slot).  Nothing produced those words.

This file produces them, twice over.

* **Physically.**  `FinalPrimeRow`'s Horner sweep is re-derived at an arbitrary
  *offset* of the bit tape (`stateFrom`, `hornerFrom`, `srcCfg`,
  `body_supplier`).  One coefficient tape then carries every coefficient of the
  row as a `K`-bit MSB-first block, and `reduction_loop` says: for each
  coefficient index `i` the driven loop `CloseoutRowsDegreeLoop.machine
  FinalPrimeRow.body`, started at offset `i * K` from the zero residue state,
  halts in `K * (4 * width + 9) + 3` ordinary steps with residue word exactly
  `SignedSortKey.binary width (c i % prime)`.  `n` coefficients are `n` passes
  of one machine on one tape: `loopFuel width K n` steps in total.  No new
  machine and no new assumption is introduced — the loop body is the accepted
  `FinalPrimeRow.body`, only its entry offset moves.

* **Arithmetically.**  `reducedWord` is the concrete stream
  `SignedSortKey.binary width ((eq.weights i) mod p)`, with `-eq.target` in the
  last slot, and `gateList` the concrete gate stream of one input.  All four
  hypotheses of `threshold_row_run` are discharged for them, so
  `threshold_row_reduced` emits `SupplierPrime.modularEquationHolds` from data
  that is *defined*, not assumed.

`reduced_of_congr` is the bridge: any physically reduced natural coefficient
congruent to the equation's integer weight produces the same word, so the two
halves name one object.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeReduce
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
open SupplierPipeline SupplierPrime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. The Horner recurrence at a tape offset -/

/-! ## 2. The sweep state at a tape offset -/

/-! ## 3. The driven loop, entered at an offset -/

/-! ## 4. The zero residue state, and the reduced word of one window -/

/-! ## 5. One coefficient tape carrying every coefficient of the row -/

/-! ## 6. The loop -/

/-! ## 7. The reduced stream of one labelled equation -/

/-- The canonical representative of an integer residue class below the prime. -/
def intResidue (p : ℕ) (z : ℤ) : ℕ := (z % (p : ℤ)).toNat

/-! ## 8. The threshold row with the reduced stream supplied -/

/-! ## 9. Rung 2, THR mode, with nothing about the stream assumed -/

section PaperRow
open SourceInterfaces RepairRepresentation SupplierEstimator RepairSource.CloseoutRawRows

end PaperRow

end NearCubicWires.RepairOrdinary.FinalPrimeReduce
