import Proof.MachineModel.BankCaseTwoEnvelopeClosure
import Proof.Circuits.SelectorDrivenBodyClosure

/-!
# Programs and envelopes for direct inverse selector target chains

The selector body already starts at scheduled numeral registers.  These two
programs are the register-driven branch bodies without the old
request-length-indexed `uniformTargetProgram` wrapper, and the two maxima are
their shared dispatcher envelope.
-/

namespace NearCubicWires.SelectorDrivenRegisterTargetChainBase

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

end NearCubicWires.SelectorDrivenRegisterTargetChainBase
