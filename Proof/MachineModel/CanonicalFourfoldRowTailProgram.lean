import Proof.Supplier.FourfoldRangeAggregationComposition

/-!
# The executable fourfold row tail and its envelope front end

`FourfoldRangeAggregationComposition` reduces the two execution fields of
`SharedNormalizedAggregationArtifact` to one *row tail*: a machine from the
exact-bottom package produced by `fourfoldRangeBottomProgram` to the Boolean
row code.  This module supplies that tail's fixed structure and the matching
front end, so the whole chain

```text
typed envelope -> balanced range input -> all-row aggregation -> component
```

is a single linked `NPOracleProgram` with an exact run theorem in precisely
the shape `SharedNormalizedAggregationArtifact.computesSymmetric` and
`…computesThreshold` consume.

Two link-time program parameters remain, each with an exact interpreter
premise and no fuel or callback argument:

* `rowEvaluator`, on the native five-field row handoff paired with the exact
  bottom forest, computing `boolCode (evaluateCanonicalFourfoldRow …)`;
* `countProgram`, on the typed envelope, computing the row-major atom count.

Everything between them — the bottom-package repack, the family-tag decode,
the denominator tail, and the balanced range input — is executed here, with
closed width and fuel envelopes.
-/

namespace NearCubicWires.CanonicalFourfoldRowTailProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRangeRequestProgram
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRangeAggregationComposition
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §1 The row-tail repack -/

/-! ## §2 The linked row tail -/

/-! ## §3 The two published row-tail specializations

These are exactly the `htail` premises of
`run_symmetricRowCalleeProgram_of_rowTail` and
`run_thresholdRowCalleeProgram_of_rowTail`, discharged from one exact
evaluator run on the native handoff. -/

/-! ## §4 The compiled Boolean row callee

The aggregation controller charges its callee a fuel that depends only on the
generated range atom, so the tail fuel is re-expressed through the atom's own
projections. -/

/-! ## §5 The compiled all-row aggregation component -/

/-! ## §6 The envelope front end

The aggregation controller starts from `generatedBalancedRangeInput`, while
the artifact's public entry point is the typed envelope.  This section
executes the missing prefix: recover the family tag as a native number, build
the opaque row context, obtain the row-major atom count from one link-time
counter, and emit the denominator tail beside it. -/

/-! ## §7 One program from the typed envelope to the ratio component

This is the shape `SharedNormalizedAggregationArtifact.computesSymmetric` and
`…computesThreshold` consume.  The program is fixed once for both modes: the
family tag is decoded from the request, never supplied. -/

/-! ## §8 Splitting the row residual by published family

The artifact holds one program for both published families, so the row
evaluator above must serve both.  This section removes that coupling: the
canonical mode code already sits at the head of the row handoff, so a fixed
hoist plus the verified tag dispatcher reduces the single residual to one
evaluator per family.  Composing `run_fourfoldRowModeDispatchProgram_*` with
the `hevaluator` premise of §5 and §7 needs no further glue. -/

end NearCubicWires.CanonicalFourfoldRowTailProgram
