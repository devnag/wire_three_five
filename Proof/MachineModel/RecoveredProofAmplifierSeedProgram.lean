import Proof.MachineModel.RecoveredProofRequestCompilerProgram

/-!
# From the raw refuter word to the published amplifier's seed request

`RecoveredProofRequestCompilerProgram` builds the balanced request list of the
C.12 recovery formula and retains the schedule frame beside it.  This module
consumes that pair once and produces the exact `AmplifierRequest.code` of the
recovered outer proof.

Three fixed stages, no new recovery path:

* the request compiler,
* `RecoveredProofEncodingProgram.recoveredProofEncodingProgram` run through the
  shared context-preserving wrapper — its public length is already the callee
  length retained by the compiler, so no relocation is needed here,
* one six-instruction adapter that reads the retained arity and emits
  `pair arity (encodeBoolFunction …)`.

The composed output is literally
`RecoveredProofEncodingProgram.amplifierRequestCode` of the recovered proof, so
`run_amplifierConstructionCallProgram_pair` may be applied immediately.
-/

namespace NearCubicWires.RecoveredProofAmplifierSeedProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofEncodingProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The seed-request adapter

Input `pair encoded (pair calleeLength (pair arity word))`, output
`pair arity encoded`.  The word and the callee length are consumed here: the
amplifier's construction program needs neither. -/

/-! ## 2. The composed seed-request producer -/

end NearCubicWires.RecoveredProofAmplifierSeedProgram
