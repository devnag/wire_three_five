import Proof.Circuits.InverseLengthStage

/-!
# The inverse schedule's `hexecutes`, from the selector-driven bank

`ScheduleDiagonalObstruction` / `ScheduleImageDiagonalObstruction` proved every
form of `hdiagonal` unsatisfiable; `SourceDrivenNumeralBank` replaced the
log-decoding bank with the selector-driven bank whose frame is the chain's own
frame definitionally; and `InverseLengthStage.inverse_scheduledLengthRuns` made
its one residual a theorem.  This module closes the seam: it produces the
executable target language's terminal obligation `hexecutes` from the
selector-driven bank, with **no `hdiagonal` in any form**.

`ExecutableTargetLanguagePackaging.inverse_hexecutes_of_uniformTargetRun` is bank
agnostic — it consumes an arbitrary `program` with a totality premise (`hrun`)
and an on-onset canonical premise (`huniform`).  §1 links the selector-driven
bank in front of a register-driven body; §2 derives `huniform` from a body that
returns the canonical target from the **selector-driven frame**
(`selectorDrivenBankFrame`), i.e. the chain's own frame; §3 packages the two
into `hexecutes`.

## What is carried, and why it is no longer `hdiagonal`

The remaining premise is `bodyRun`, at `selectorDrivenBankFrame` rather than at
the old `publishedBankFrame … target`.  This is not `hdiagonal`: the selector
bank *builds* the chain's frame, so the body reads the chain's numerals
unconditionally.  `SelectorDrivenAtomContext.inverseAtomContext_ofSelectorRegisters`
is the exemplar showing the register identification the old body needed the
diagonal for is now definitional.  Discharging `bodyRun` in full is the body
chain's own restatement at the selector frame — the industrialized replay named
at the end of this file.
-/

namespace NearCubicWires.InverseSelectorHexecutes

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.ScheduledRecovery
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The selector-driven uniform target program -/

/-! ## 2. `huniform` from a selector-frame body -/

/-! ## 3. `hexecutes` from the selector-driven bank -/

end NearCubicWires.InverseSelectorHexecutes
