import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalFourfoldRowTailProgram

/-!
# The row-major atom counter of a fourfold range request

`CanonicalFourfoldRowTailProgram` reduces the composed aggregation program to
two link-time parameters.  This module discharges the *product* half of the
second one.

The envelope front end needs the row-major atom count

```text
fourfoldRangeAtomCount rows request = rows.rowCount request * 2 ^ request.q
```

as a machine value computed from the typed envelope alone.  The arity `q` is
already present in the interpreter's public length register, so the second
factor never has to be parsed: this module supplies the fixed doubling loop
that materializes `2 ^ q` from that register, pairs it with a link-time row
count, and multiplies with the existing bit-serial multiplier.

Consequently the residual on the counting side is exactly one program: an
`NPOracleProgram` computing `rows.rowCount request` from the typed envelope.
Nothing here assumes a semantic evaluator, a callback, or a fuel argument.
-/

namespace NearCubicWires.CanonicalFourfoldRowCountProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 Materializing `2 ^ q` beside the row count

The interpreter's register `r1` holds the public input length on entry to
every linked stage, so the arity is available without decoding the envelope a
second time.  Registers `r2` and `r3` are the loop cursor and accumulator. -/

/-! ## §2 The linked atom counter -/

/-! ## §3 The two published specializations

These are exactly the `hcount` premises of
`run_sharedFourfoldAggregationProgram_symmetric` and
`…_threshold`, with the remaining obligation reduced to the row count of one
published family. -/

end NearCubicWires.CanonicalFourfoldRowCountProgram
