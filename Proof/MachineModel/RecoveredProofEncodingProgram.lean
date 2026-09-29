import Proof.MachineModel.BoundedOracleRecoveryProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.Amplification.CaseOneRecoveryAssembly

/-!
# The recovered accepting proof as one encoded truth table

Case 1 of the canonical target language has to hand the published amplifier a
whole `AmplifierRequest`, whose code contains `encodeBoolFunction` of the
exponentially long C.12-recovered outer proof.  This module fixes that
producer.

There is no new recovery path here.  The callee is the already verified
zero-first prefix-SAT reducer `rawClausePrefixSATProgram`, applied once per
address of the recovered proof through the single balanced call ABI of
`CanonicalBalancedCall`.  Because that ABI already returns
`encodeBalancedList` of the per-request outputs and `encodeBoolFunction` is by
definition `encodeBalancedList` of the Boolean codes of the truth table, the
loop's certified output is literally the amplifier's request payload.

Two seams are closed.

* `run_recoveredProofEncodingProgram` — one fixed program, explicit width and
  fuel, whose output is `encodeBoolFunction (recoveredOuterProofFunction …)`.
* `run_amplifierConstructionCallProgram` — the single native call that turns
  that payload into the published amplifier's own `outputArity` and
  `descriptor`, which are the two data arguments still supplied by hand to
  `CanonicalTargetLanguageProgram.run_targetBitProgram_inverseCaseOne`.
-/

namespace NearCubicWires.RecoveredProofEncodingProgram

open NearCubicWires
open NearCubicWires.BoundedOracleRecoveryProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. Small arithmetic facts about one recovered bit -/

/-! ## 2. The fixed request schedule of the recovered proof -/

/-! ## 3. The fixed encoding loop -/

/-! ## 4. Scheduled instance and the amplifier construction call -/

/-- The exact `AmplifierRequest` code of one seed. -/
def amplifierRequestCode {arity : ℕ} (seed : BoolFunction arity) : ℕ :=
  Nat.pair arity (encodeBoolFunction seed)

@[simp] theorem amplifierRequestCode_eq {arity : ℕ}
    (seed : BoolFunction arity) :
    AmplifierRequest.code ⟨arity, seed⟩ = amplifierRequestCode seed :=
  rfl

end NearCubicWires.RecoveredProofEncodingProgram
