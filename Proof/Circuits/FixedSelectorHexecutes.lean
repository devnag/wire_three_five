import Proof.Circuits.SelectorDrivenLengthStage
import Proof.Circuits.UniformTargetTotalRun

/-!
# The fixed schedule's `hexecutes`, from the selector-driven bank

The fixed length stage already runs the schedule selector and constructs the
chain's own numeral frame with no diagonal premise.  This module links that
closed bank to an arbitrary register-driven body and packages the resulting
canonical run as the exact fixed-schedule `hexecutes` obligation.
-/

namespace NearCubicWires.FixedSelectorHexecutes

open NearCubicWires
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenLengthStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.UniformTargetTotalRun
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed selector-driven uniform target program -/

/-! ## 1b. Totality through the closed fixed selector bank -/

/-! ## 2. Canonical linked runs from a selector-frame body -/

/-! ## 3. Terminal fixed `hexecutes` -/

/-! ## 4. The headline-shaped one-totality interface -/

end NearCubicWires.FixedSelectorHexecutes
