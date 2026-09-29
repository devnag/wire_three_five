import Proof.CaseAnalysis.CaseTwoCanonicalCircuitEncoder
import Proof.Circuits.FixedSelectorAtomContextRuns
import Proof.Circuits.SelectorDrivenLengthStage

/-!
# Fixed description-request source adapter

The selector-driven numeral bank loads its closed frame from the public target.
The ordinary linker then enters one frame-local body with the same public input
length in `r1`.  This module exposes only that ABI seam and the canonical
circuit-description request it returns.
-/

namespace NearCubicWires.FixedDescriptionRequestSourceAdapter

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedSelectorAtomContextReplay
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenLengthStage
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The public target-code firewall -/

/-! ## 2. The exact description request -/

/-! ## 3. Load the selector frame from `(target, target)` -/

end NearCubicWires.FixedDescriptionRequestSourceAdapter
