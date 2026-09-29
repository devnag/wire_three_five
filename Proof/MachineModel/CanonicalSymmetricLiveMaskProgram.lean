import Proof.MachineModel.CanonicalSymmetricRowTableProgram
import Proof.MachineModel.CanonicalSymmetricTouchingCostProgram

/-!
# The symmetric row's live mask, executed from the typed envelope

`CanonicalSymmetricRowTableProgram` carries the greedy live-set selector only
through the abstract equation

```text
    hlive : liveMask = coordinateMask (symmetricRowLiveSet request liveScale)
```

so every row theorem is stated for *some* natural number that happens to be
that mask.  `CanonicalSymmetricTouchingCostProgram` already runs the whole
greedy conditional-expectation sweep on the envelope's support-mask tree; its
cost pipeline discards the selected mask one stage after producing it.

This module keeps that mask instead.  The first five stages are exactly the
touching-cost pipeline's; the sixth is a three-instruction projection of the
sweep's final carried state.  The result is one oracle-free program computing
`coordinateMask (symmetricRowLiveSet request liveScale)` from
`symmetricEnvelopeCode request`, so `hlive` is no longer an assumption about an
uncomputed quantity: §3 instantiates the symmetric row evaluator at the mask
this program returns, with `hlive` discharged by `rfl`.
-/

open Finset

namespace NearCubicWires.CanonicalSymmetricLiveMaskProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.CanonicalSymmetricRowTableProgram
open NearCubicWires.CanonicalSymmetricSupportMaskProgram
open NearCubicWires.CanonicalSymmetricTouchingCostProgram
open NearCubicWires.CanonicalTouchingSweepProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

/-! ## §1 The sweep's selected mask

The sweep's carried state is `pair context (pair selectedMask stepCount)`, so
keeping the selection is two `unpair` instructions. -/

/-! ## §2 The live mask, executed from the typed envelope

Six linked stages: the pool's support-mask tree, the sweep's live budget, the
sweep's public input, the counted round call itself, and §1. -/

/-! ## §3 The row evaluator at the computed mask

Instantiating `CanonicalSymmetricRowTableProgram` at the mask §2 returns
discharges `hlive` by `rfl`, so the symmetric row evaluator's remaining
premises are exactly the two producer contracts. -/

end NearCubicWires.CanonicalSymmetricLiveMaskProgram
