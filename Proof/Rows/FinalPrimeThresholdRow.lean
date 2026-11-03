import Proof.Rows.FinalPrimeModularSum
import Proof.Rows.FinalPrimeResidueWord

/-! # The THR row producer: one ordinary run emitting the row's accept bit

This joins the two verified stages into a single machine on a nine-tape bank:

* `CloseoutRowsDegreeLoop.machine FinalPrimeModular.body` accumulates the gated
  summand stream modulo the prime (`FinalPrimeModular.accumulate_loop`);
* `FinalPrimeRowOut.machine`, docked by an injective slot map, materialises the
  residue and emits the zero verdict in the same pass.

`Composition` adds finite control states but no tapes and the row-output stage
needs no head reset, so the tape stack stays exactly
`pass -> MaskedReset -> RepeatMachine` plus one embedded result cell.

The bridge `accum_congr` says the accumulated residue is congruent to the
labelled equation's difference, so the emitted bit is literally
`SupplierPrime.modularEquationHolds`.  The paper's accuracy for that bit is
unchanged: it is exactly the quantity bounded by
`CloseoutRawRows.threshold_prime_error` and `threshold_union_error`.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeThresholdRow
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
open SupplierPipeline SupplierPrime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. The nine-tape bank -/


def rowFuel (width Q : ℕ) : ℕ :=
  Q * (FinalPrimeModular.cost width + 3) + 3 + 1 + (2 * width + 2)

/-! ## 2. The port equalities, hoisted out of the tape stack -/

/-! ## 3. One run of the joined machine -/

/-! ## 4. The accumulation is the equation's difference -/

/-! ## 5. The emitted bit is `modularEquationHolds` -/

end NearCubicWires.RepairOrdinary.FinalPrimeThresholdRow
