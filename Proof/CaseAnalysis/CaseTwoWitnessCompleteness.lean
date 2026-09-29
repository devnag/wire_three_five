import Proof.MachineModel.CanonicalRecoveryProgram
import Proof.Amplification.RecoveryWitnessScheduleCapacity
import Proof.PCP.VerifierThresholdSeam

/-!
# Case-2 witness completeness for the fixed recovery machine

This module discharges the mathematical content of the Case-2 completeness
obligation `hcaseTwo`, namely `InverseCaseTwoAcceptance` and
`FixedCaseTwoAcceptance` of
[`CaseTwoRecoveryAssembly`](Proof/Amplification/CaseTwoRecoveryAssembly.lean).

The construction is witness-first.  From one legal symmetric or threshold
approximation of the scheduled Case-2 seed it builds the canonical
`CheckedRecoveryWitness` at the schedule-selected `RecoveryWitnessLimits`,
widens it into the sole length-indexed verifier policy without changing a
single serialized bit, places its canonical code into the fixed `n / 16`
nondeterministic witness using the existing schedule-capacity theorem, and
reads that code back exactly.

The semantic approximation distance is deliberately *not* stored in
`CheckedRecoveryWitness`; the verifier must execute that check itself.  This
module therefore keeps the distance alive as a separate proposition,
`RecoveryWitnessApproximates`, proved for the constructed witness from the
pointwise value theorems of `RecoveryWitnessNormalization`.  Nothing here
recovers the distance from a proof field of the witness.

## The single remaining machine hypothesis

Everything above is unconditional.  The only fact that cannot be proved before
the concrete machine exists is the behaviour of its verifier program on the
accepting witness.  It is isolated in exactly one definition,
`RecoveryVerifierAcceptsApproximation`:

```lean
∀ bits : BitInput (machine.witnessBits inputLength),
  recoveryWitnessValidatorOutput limits (encodeBitInput bits) ≠ 0 →
  (∀ witness : CheckedRecoveryWitness limits,
    decodeRecoveryWitness limits (encodeBitInput bits) = some witness →
    RecoveryWitnessApproximates seed delta witness) →
  machine.verifier.execute (machine.verifierRequest input bits) ≠ 0
```

Both premises are discharged here for the constructed witness: the guessed raw
code is accepted by the *pure* full-validator specification
`recoveryWitnessValidatorOutput` of `CanonicalRecoveryProgram`, see
`recoveryWitnessValidatorOutput_ne_zero_of_readback`, and every witness that
specification can return passes the semantic approximation check.  The
conclusion is one run of the verifier program on the corresponding
`WeakVerifierRequest`; no local checker, callback, evaluator, or fuel argument
occurs.  When the concrete machine lands, the hypothesis is discharged by
substitution from the verifier's run theorem.

`not_recoveryWitnessApproximates_of_checked` at the end of this module is the
regression guard for the failure mode the handoff calls out: a fully checked
canonical witness carries no distance evidence, so completeness cannot be
obtained from a supplied `CheckedRecoveryWitness`.
-/

namespace NearCubicWires.CaseTwoWitnessCompleteness

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessNormalization
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessScheduleCapacity
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-! ## Semantic value of one serialized legal sum

The value depends only on the serialized description, never on the resource
policy it was checked against.  Keeping the limits out of this definition is
what lets the same real-valued function be recognized before and after a
policy widening. -/

/-! ## The approximation check the verifier must execute -/

/-! ## Canonical witness construction that keeps the distance alive -/

/-! ## Policy widening preserves the executed check -/

/-! ## The single remaining machine hypothesis -/

/-! ## Inverse-polynomial schedule -/

/-! ## Fixed-rate schedule -/

/-! ## Exact `hcaseTwo` shapes at the published refuter word -/

/-! ## Alignment with the verifier threshold seam

`VerifierThresholdSeam.§7` refutes the published fixed radius `1 / 4`: the
verifier's completeness direction needs `delta ≤ 3 * zeta`, and the soundness
reserve forces `6 * zeta < 1 / 288`.  `§9` closes the seam at
`repairedRecoveryDelta parameters = parameters.zeta`.  The three theorems below
compile the statement that this module's Case-2 chain — the one that ends in
`inverseCaseTwoAcceptance_at_refuterInput` and
`fixedCaseTwoAcceptance_at_refuterInput` — now runs at exactly that radius, so
the `RecoveryWitnessApproximates seed (publishedRecoveryDelta contracts)`
premise it carries and the `hclose` premise of
`repairedDelta_completeness_seam` are the same hypothesis. -/

/-! ## Regression: the executed check is not stored evidence

The following closed counterexample is a guard against a completeness proof
that reads the approximation distance out of a supplied
`CheckedRecoveryWitness`.  Every resource check of the policy succeeds while
the semantic check fails, so the distance is genuinely additional information
that the verifier must compute. -/

end NearCubicWires.CaseTwoWitnessCompleteness
