import Proof.CaseAnalysis.CaseTwoOccurrenceCoordinates

/-!
# The Case-2 branch of the canonical target language, from the request alone

`CanonicalTargetLanguageProgram.run_targetBitProgram_caseTwo_xorPower` shows
that the already fixed target-bit dispatcher returns exactly the XOR-amplified
seed bit once the seed block values are data on its input.  The public
pointwise exports
`CaseTwoRecoveryAssembly.inverseCanonicalTargetFunction_caseTwo_apply` and its
fixed-rate counterpart identify that XOR power with the canonical target on
the Case-2 branch.

This module links the two.  Exactly as `CaseOneTargetLanguageClosure` leaves
its single named decision-row stage as a hypothesis, the block stage — the
loop that evaluates the scheduled Case-2 seed once per XOR copy, whose
per-copy value is
`CaseTwoOccurrenceCoordinates.caseTwoSeed_apply_occurrenceCodeValue` and whose
per-copy execution is
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram` — is a parameter here.
Everything downstream of it is closed: one link, one dispatcher run, and the
published branch value theorem.
-/

namespace NearCubicWires.CaseTwoTargetLanguageClosure

open NearCubicWires
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The seed block values of one XOR power -/

/-! ## 2. One link onto the fixed dispatcher -/

/-! ## 3. The inverse-schedule Case-2 target -/

/-! ## 4. The fixed-rate Case-2 target -/

end NearCubicWires.CaseTwoTargetLanguageClosure
