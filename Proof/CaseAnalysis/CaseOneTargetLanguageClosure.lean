import Proof.MachineModel.OuterProofRecoveryFormulaSeedProgram
import Proof.MachineModel.RecoveredProofCaseOneProgram
import Proof.MachineModel.RefuterWordFrameProgram

/-!
# The Case-1 branch of the canonical target language, from the request alone

Three fixed stages now separate a `LanguageEvaluationRequest`'s point code from
the canonical Case-1 target bit:

* `RefuterWordFrameProgram` builds the refuter-word frame with one published
  refuter call;
* `OuterProofRecoveryFormulaSeedProgram` builds the C.12 recovery seed from
  that frame's word, modulo the single named decision-row stage;
* `RecoveredProofCaseOneProgram` compiles the recovery request list, encodes
  the recovered proof, calls the published amplifier's construction program,
  and runs the fixed target-bit dispatcher.

This module links the first stage onto the last two.  The composed program is
parameterized only by numerals — the machine description, the scheduled source
length, and the scheduled width — plus the one named row stage; the sole
remaining hypothesis of its exact-execution theorem is that row stage's own run
theorem together with the already published target-bit run.
-/

namespace NearCubicWires.CaseOneTargetLanguageClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RefuterWordFrameProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

end NearCubicWires.CaseOneTargetLanguageClosure
