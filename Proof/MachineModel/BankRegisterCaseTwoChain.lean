import Proof.MachineModel.BankRegisterCaseOneChain

/-!
# The Case-2 chain at the requested point code

`BankFramedTargetChains.inverse_chainTwo_ofPointRuns` reduces the dispatcher's
Case-2 premise to `InverseCaseTwoPointRuns`: one **fixed** instruction stream
returning the canonical target bit from the requested point code.

`BankCaseTwoSeedBlockListProgram.run_bankCaseTwoTargetBitProgram_inverse`
already runs the whole Case-2 branch from the numeral bank's frame with the XOR
copy count read out of a register rather than baked, so on that side the chain
is target uniform outright — mirroring
`EmittedBranchTargetProgram.fixedCaseTwoChainProgram_target_independent`, which
records the same for the fixed schedule.  §1 puts the published numeral bank in
front of it, so the stream starts at the bare point code, and §3 discharges
`InverseCaseTwoPointRuns`.

## What is left, exactly

One correctness premise, `InverseScheduledOccurrenceRuns`: the per-block
occurrence callee of `CaseTwoSeedBlockListProgram`, at every block below the
scheduled copy count.  That callee is the one stage that still bakes
`CanonicalTargetLanguageProgram.caseTwoSubstitutedCircuit caseTwo`, an object
recovered from the accepting oracle and therefore genuinely request-dependent;
removing it means computing the substituted circuit at run time from the
compiled substitution substrate
(`CanonicalStructuralGF2SubstituteProgram`,
`CanonicalStructuralGF2TruthTableProgram.structuralGF2BitMajority_eq_substitute`),
which is not attempted here.

Beside it, one resource premise `InverseCaseTwoBankEnvelopes`: the shared chain
envelopes of the dispatcher must dominate the register-driven Case-2 envelopes.
The dispatcher shares one width and one fuel function between both branches, so
a domination statement is the only way to state the Case-2 side without letting
the branch's own accepting oracle leak into a public resource function.
-/

namespace NearCubicWires.BankRegisterCaseTwoChain

open NearCubicWires
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The chain from the requested point code -/

/-! ## 2. The two residual premises -/

/-! ## 3. `InverseCaseTwoPointRuns`, discharged -/

end NearCubicWires.BankRegisterCaseTwoChain
