import Proof.Circuits.SelectorDrivenRegisterTargetChainBase

/-!
# Direct inverse Case-one chain at selector-driven registers

This is the Case-one half of the direct selector-chain join.  The selector
frame already carries the scheduled source length, width, query count, and copy
count, so the register-driven body needs no schedule diagonal.  Its sole
honest residual is `InverseScheduledRowRuns`.
-/

namespace NearCubicWires.SelectorDrivenRegisterCaseOneChain

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

end NearCubicWires.SelectorDrivenRegisterCaseOneChain
