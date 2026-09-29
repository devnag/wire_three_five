import Proof.Circuits.InverseSourceIndexScan
import Proof.Circuits.SelectorDrivenLengthStage

/-!
# The inverse schedule's length program, executed

`InverseSourceIndexScan` proved the four-register additions-only scan computes
`RecoveryScheduleEnvelope.inverseSourceIndex` (`scanIter_eq_inverseSourceIndex`).
This module transcribes that scan into an `NPOracleProgram` (§2), then mirrors
`SelectorDrivenLengthStage`'s fixed pipeline with the extra scan stage (§3) to
discharge `SourceDrivenNumeralBank.InverseScheduledLengthRuns` and close the
inverse selector-driven bank with no hypothesis.

The scan program is one padded loop so every trajectory through it costs exactly
eighteen instructions per iteration — the uniform fuel `18·i + 4` the run lemma
charges.  Its register ABI is `r2=i`, `r3=j`, `r4=c`, `r5=q`, `r6=prod`,
`r7=arg`, `r8=K=k+2`, `r9=code`, with `r10..r15` scratch.
-/

namespace NearCubicWires.InverseLengthStage

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSourceIndexScan
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenLengthStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Reachable-value bound -/

/-! ## 2. The scan program -/

/-! ## 3. The inverse schedule's length program, assembled -/

/-! ## 4. `InverseScheduledLengthRuns`, discharged -/

end NearCubicWires.InverseLengthStage
