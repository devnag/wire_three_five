import Proof.CaseAnalysis.FixedRegisterCaseOneChain
import Proof.Circuits.FixedSelectorFramedTargetChains
import Proof.Circuits.FixedSelectorHexecutes

/-!
# The fixed Case-1 point run through the selector bank

`FixedRegisterCaseOneChain.fixedCaseOnePointRuns_ofRow` used the old
length-decoded numeral bank and therefore required the false schedule diagonal.
The register-driven Case-1 body itself is frame-parametric.  Prefixing it with
the fixed selector bank supplies its own source length and width registers, so
the same row residual gives the raw point run with no diagonal.
-/

namespace NearCubicWires.FixedSelectorCaseOnePointRunsOfRow

open NearCubicWires
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedRegisterCaseOneChain
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.FixedSelectorFramedTargetChains
open NearCubicWires.FixedSelectorHexecutes
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

/-! ## 1. The selector-prefixed Case-1 chain -/

/-! ## 2. The raw fixed Case-1 point contract -/

end NearCubicWires.FixedSelectorCaseOnePointRunsOfRow
