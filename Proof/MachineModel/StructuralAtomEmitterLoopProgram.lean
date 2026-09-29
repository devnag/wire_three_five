import Proof.MachineModel.BankRecoveryCodeProgram
import Proof.Circuits.BoundedOracleStructuralFormulaTable
import Proof.MachineModel.CanonicalBalancedFlattenProgram

/-!
# The structural atom emitter as a generated range loop

`BankRecoveryCodeProgram.run_emittedBranchSelectorProgram` reduces the whole
branch query of `CanonicalBranchSelectorProgram` to one named program parameter
`emitter` with one named run hypothesis: from the request's own code the
emitter must return

`pair (encodeTaggedList (boundedOracleStructuralFormulaAtoms pcp word bound))
  pointCode`.

That premise is *list-valued*, which is the wrong shape for the audited
pointwise structural callee of `BoundedOracleStructuralSelectiveProgram`: that
callee answers one global formula index at a time.

This module supplies the missing loop.  It is the idiom
`OuterProofRecoveryFormulaSeedProgram` and `ProjectionRunnerBalancedProgram`
already use: `GeneratedBalancedRangeProgram` materializes the index requests
directly in the canonical balanced representation, `CanonicalBalancedCall` runs
one callee per request, and `CanonicalBalancedFlattenProgram` converts the
resulting balanced list into the tagged stream the recovery-code assembler
consumes.  Two `preserveRightProgram` wrappers carry the request's point code
past both halves untouched.

The result (§3, §4) replaces the list-valued emitter premise by the *pointwise*
one: one run of one callee per global formula index.  §5 feeds it straight into
`BankRecoveryCodeProgram`, so the branch query of any executable projection PCP
is decided with no immediate and with a single per-index hypothesis.

## What is still open

The pointwise callee itself — `BoundedOracleStructuralSelectiveProgram.structuralFormulaProgram` —
carries its own compiler-execution premise: `selectiveCountCasesProgram` has no
run theorem, so the per-index hypothesis below cannot yet be discharged from
that module.  This loop is exactly the reduction from a list statement to that
per-index statement; it does not attempt to prove the per-index statement.
-/

namespace NearCubicWires.StructuralAtomEmitterLoopProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedFlattenProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Dropping the context the range generator retains -/

/-! ## 2. The generated index loop -/

/-! ## 3. The emitter: the loop's list, retagged, beside the point code -/

/-! ## 4. The structural formula atoms of an executable projection PCP -/

/-! ## 5. The branch query, decided from the pointwise callee -/

end NearCubicWires.StructuralAtomEmitterLoopProgram
