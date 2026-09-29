import Proof.MachineModel.CanonicalTargetLanguageProgram
import Proof.MachineModel.RecoveredProofAmplifierSeedProgram

/-!
# The Case-1 half of the executable target language

Everything Case 1 needs is now a fixed instruction stream.  This module links
the five stages into one program and one exact run theorem.

1. `nativeContextCallProgram (recoveredProofAmplifierSeedProgram seed)` — the
   whole recovery is run once at the *source* input length while the outer
   program keeps the public target length, and the requested point code is
   preserved beside the result.
2. A seven-instruction frame adapter producing the canonical native request of
   the published amplifier's construction program.
3. `preserveRightProgram (nativeCallProgram construction.program)` — the one
   construction call of `run_amplifierConstructionCallProgram_pair`, again with
   the point code preserved.
4. An eight-instruction frame adapter producing
   `CanonicalTargetBitProgram.targetBitCaseOneInput`.
5. `targetBitProgram` itself, whose Case-1 outputs are exactly
   `inverseCaseOneTargetFunction` and `fixedCaseOneTargetFunction` by
   `CanonicalTargetLanguageProgram.run_targetBitProgram_inverseCaseOne` and
   `run_targetBitProgram_fixedCaseOne`.

The public input of the composed program is the refuter-word frame
`pair (encodeBitInput refuterWord) (pair sourceLength pointCode)`.  Producing
that frame from the point code alone is one published refuter call, the same
seam already isolated by
`CanonicalTargetLanguageProgram.inverseRefuterInput_eq_of_description`.
-/

namespace NearCubicWires.RecoveredProofCaseOneProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofAmplifierSeedProgram
open NearCubicWires.RecoveredProofEncodingProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The construction-call frame adapter

Input `pair (pair arity encoded) (pair calleeLength pointCode)`, output
`pair (nativeInputRequest arity (pair arity encoded)) pointCode`. -/

/-! ## 2. The target-bit frame adapter

Input `pair (pair outputArity descriptor) pointCode`, output
`targetBitCaseOneInput outputArity descriptor pointCode`. -/

/-! ## 3. The composed Case-1 program -/

end NearCubicWires.RecoveredProofCaseOneProgram
