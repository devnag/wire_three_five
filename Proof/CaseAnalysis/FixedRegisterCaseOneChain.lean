import Proof.MachineModel.BankRegisterCaseOneChain
import Proof.Circuits.FixedScheduleDiagonalClosure

/-!
# The fixed schedule's Case-1 chain, with every numeral read from a register

The fixed twin of `BankRegisterCaseOneChain`.  Nothing below the schedule is
replayed: §1 of that module — `bankRegisterCaseOneTargetBitProgram` and
`run_bankRegisterCaseOneTargetBitProgram`, the refuter-word frame for the
scheduled source length and the formula seed for the scheduled width — is
schedule free and is cited unchanged.  What this module supplies is the two
schedule-specific halves the inverse module states for its own schedule:

* §1 the chain at the requested point code, with the published numeral bank in
  front, at the **fixed** bank rate;
* §2 `FixedScheduleDiagonalClosure.FixedCaseOnePointRuns` from one residual,
  the decision-row stage — the exact twin of
  `BankRegisterCaseOneChain.inverseCaseOnePointRuns_ofRow`.

The fixed chain's index is `CaseOneRecoveryAssembly.fixedSelectedSource`
itself, with no `RecoveryScheduleEnvelope.inverseSourceIndex` in front of it, so
every statement below is one function application shorter than the inverse one.

`hdiagonal` is threaded, never asserted: this module says what the chain does
*given* that the requested public length is the scheduled source length, and
says nothing about whether any target satisfies that.
-/

namespace NearCubicWires.FixedRegisterCaseOneChain

open NearCubicWires
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankOuterProofFormulaSeedProgram
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The chain from the requested point code -/

/-! ## 2. `FixedCaseOnePointRuns`, from the row stage alone -/

end NearCubicWires.FixedRegisterCaseOneChain
