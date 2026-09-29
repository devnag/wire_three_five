import Proof.MachineModel.BoundedOracleStructuralSelectiveProgram
import Proof.MachineModel.StructuralAtomEmitterLoopProgram

/-!
# The pointwise structural callee of the atom loop

`StructuralAtomEmitterLoopProgram` reduces the whole branch query of
`CanonicalBranchSelectorProgram` to *one* per-index hypothesis: at every global
formula index the loop's callee, started on the generated request body
`pair index context`, must return the canonical structural atom at that index.

This module supplies that callee.  It is the audited pointwise runner
`BoundedOracleStructuralSelectiveProgram.structuralFormulaProgram` followed by
one two-instruction projection: the runner answers with the pair
`(formula length, atom)`, and the loop consumes the atom alone.

The runner itself is executed by
`BoundedOracleStructuralSelectiveProgram.run_structuralFormulaProgram_of_compiler_run`
modulo exactly one premise — the run of the nested structural compiler
`selectiveCountCasesProgram` on its own ABI frame.  Everything below therefore
carries that single premise, once per global formula index, and nothing else:
§3 discharges the loop's per-index hypothesis from it, §4 runs the whole
emitter from it, and §5 decides the branch query from it.

Every stage here is stated at an arbitrary public input length.  The loop of
`StructuralAtomEmitterLoopProgram` fixes it to the length of the PCP's own
input; the recovery pipeline runs the same stream at the *request's* length, and
§4 is proved at that generality so both callers are covered.

## What is still open

`selectiveCountCasesProgram` has no run theorem.  It is the nested structural
compiler as one 3023-instruction stream, and its refinement of
`BoundedOracleStructuralSelectiveCompiler.selectiveCompileTableBoundedOracleVerifier`
is the sole remaining obligation of the emitter chain; the hypothesis
`StructuralCompilerRunsAt` below is exactly that statement at one index.
-/

namespace NearCubicWires.StructuralAtomCalleeProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The response projection -/

/-! ## 2. The callee, executed from the compiler's run -/

/-! ## 3. The loop's per-index hypothesis -/

/-! ## 4. The structural atom emitter at any public length -/

/-! ## 5. The branch query, decided from the compiler's run -/

end NearCubicWires.StructuralAtomCalleeProgram
