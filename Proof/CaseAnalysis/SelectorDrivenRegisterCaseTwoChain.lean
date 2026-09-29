import Proof.Circuits.SelectorDrivenRegisterTargetChainBase

/-!
# Direct inverse Case-two chain at selector-driven registers

The generic register-driven Case-two theorem already accepts arbitrary source
length, width, and query-count registers.  Specializing those registers to
`inverseSelectorAdapterFrame` removes the old schedule diagonal.  The only
honest residual is the per-block scheduled occurrence run.
-/

namespace NearCubicWires.SelectorDrivenRegisterCaseTwoChain

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
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

end NearCubicWires.SelectorDrivenRegisterCaseTwoChain
