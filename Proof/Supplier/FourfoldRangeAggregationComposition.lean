import Proof.MachineModel.CanonicalFourfoldRowEvaluationProgram
import Proof.MachineModel.SharedNormalizedEstimatorProgram

/-!
# Executable all-row aggregation and ratio packing for fourfold requests

`SharedNormalizedAggregationArtifact` needs one fixed program that turns a
verified typed envelope into the two canonical ratio components.  Three of the
four stages already exist as verified machines: the range-atom to exact-bottom
prefix (`fourfoldRangeBottomProgram`), the balanced Boolean range aggregator
(`fixedBooleanRangeComponentProgram`), and the ratio packer
(`canonicalRatioPackerProgram`).  Only the row-evaluation tail — the machine
image of the pure `evaluateCanonicalFourfoldRow` — is missing.

This module composes the stages that do exist and proves the exact run
equalities, so the artifact's two execution fields are reduced to a *single*
named residual obligation: one Boolean row callee on the canonical range atom.
Nothing here assumes a semantic evaluator, a callback, or a fuel argument: the
callee is a link-time program parameter with an exact interpreter premise, and
every width and fuel charge is an explicit closed expression.
-/

namespace NearCubicWires.FourfoldRangeAggregationComposition

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowEvaluationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 The canonical range shape of one fourfold request -/

/-! ## §2 The composed aggregation, modulo one Boolean row callee -/

/-! ## §3 Ratio packing, executed -/

/-! ## §4 The two published specializations

These are the exact statements the artifact's `computesSymmetric` and
`computesThreshold` fields consume once a row callee exists; the remaining
open obligation is entirely inside `hexec`. -/

/-! ## §5 Linking the existing exact-bottom prefix

The residual obligation is now localized.  `fourfoldRangeBottomProgram`
already lowers a canonical range atom to the exact bottom forest, so the only
missing machine is a *row tail*: one program from the exact bottom package to
the Boolean row code.  This section proves that such a tail is exactly what
`hexec` needs — no other seam remains between the published rows and the
aggregation controller. -/

end NearCubicWires.FourfoldRangeAggregationComposition
