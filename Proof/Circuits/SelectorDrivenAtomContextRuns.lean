import Proof.Circuits.SelectorDrivenAtomContext

/-!
# The atom-context runs at the selector-driven frame

`BankAtomContextRegisters.inverseAtomContextRuns_ofTable` produces
`InverseAtomContextRuns` at the *log-decoded* bank frame
`inverseAdapterFrame … = publishedBankFrame … target`, threading `hdiagonal` to
identify that frame's registers with the chain's.  This module produces the
same context — the loop's public request context `inverseAtomContext … target`
— at the **selector-driven frame**
`selectorDrivenBankFrame … (inverseChainSourceIndex … target)`, with **no
`hdiagonal`**: the frame is the chain's frame by construction, and
`SelectorDrivenAtomContext.inverseAtomContext_ofSelectorRegisters` is the
`hdiagonal`-free register identification.

Only the register-width bits change (`inverseSelectorAtomContextBits`); the
program (`inverseAtomContextProgram`) and the fuel
(`inverseAtomContextFuel`) are frame-independent and reused verbatim.  This is
site 1 of the body-chain replay that deletes `hdiagonal` from the roots.
-/

namespace NearCubicWires.SelectorDrivenAtomContextRuns

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

/-! ## 1. The selector-driven adapter frame -/

/-! ## 2. The table and context runs at the selector frame -/

/-! ## 3. The atom-shape runs at the selector frame -/

/-! ## 4. The frame-adapter runs at the selector frame -/

end NearCubicWires.SelectorDrivenAtomContextRuns
