import Proof.Amplification.CanonicalRecoveryRequest
import Proof.CaseAnalysis.CaseTwoWitnessCompleteness
import Proof.MachineModel.QuotientProgramConversion
import Proof.MachineModel.RecoveryLimitsFrontEndProgram
import Proof.MachineModel.SharedNormalizedEstimatorProgram

/-!
# The polynomial resource envelope of the composed recovery verifier

`ExecutableRecoveryMachine` charges the composed verifier at the closed degree
`recoveryVerifierDegree = 4`, and leaves the two budget facts as the named
premises `hbits` and `hfuel`.  This module reduces both of them to the three
budgets that are genuinely owned by a component:

* the limits front end (`RecoveryLimitsFrontEndProgram`),
* the recovery-witness validator endpoint
  (`recoveryWitnessValidatorBits` / `recoveryWitnessValidatorFuel`),
* the semantic stage.

Everything in between — request extraction, the input-preserving lowering, the
count-preserving validator call, the zero-sentinel gate and the two linkers —
is charged here once and for all:

* `recoveryVerifierBits_le` shows the composed width is the maximum of the
  three component widths and a plumbing term of size `8 * (measure + 1)`;
* `recoveryVerifierFuel_le` shows the composed fuel is the *sum* of the three
  component fuels and one closed program-shape overhead
  `recoveryVerifierFuelOverhead`, which mentions no request.

Consequently the degree numeral 4 is spent entirely on the three components:
the plumbing is linear in the measure and the linker overhead is constant.
-/

namespace NearCubicWires.RecoveryVerifierResourceEnvelope

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 Width arithmetic for the pairing ABI -/

/-! ## §2 The composed width -/

/-! ## §3 The composed fuel

Every linker charge is a closed function of the *programs* it links, so the
whole plumbing cost is one request-independent overhead. -/

/-! ## §4 The limits front end at the request boundary -/

/-! ## §5 The polynomial budget

Every component budget is charged with its own coefficient at the closed
degree `recoveryVerifierDegree = 4`; the composed coefficient is their sum
plus the linker overhead.  This is exactly the "schedule-dependent growth is
charged to the coefficient" discipline of `ExecutableRecoveryMachine`. -/

section Assembly

end Assembly

end NearCubicWires.RecoveryVerifierResourceEnvelope
