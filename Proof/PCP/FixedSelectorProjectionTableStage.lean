import Proof.PCP.SelectorDrivenProjectionTableStage
import Proof.Circuits.FixedSelectorAtomContextRuns
import Proof.PCP.FixedProjectionTableStage

/-!
# Projection-table execution at the fixed selector frame

The native-call relocation is schedule-parametric.  This module instantiates
the already verified relocation at the fixed selector's own scheduled length.
The outer request keeps public length `target`; the callee reads
`fixedScheduleLength … target` from the selector frame.  No diagonal equality
is used.
-/

namespace NearCubicWires.FixedSelectorProjectionTableStage

open NearCubicWires
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedProjectionTableStage
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedSelectorAtomContextReplay
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenProjectionTableStage
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

/-! ## 1. Fixed instantiation of the relocated table program -/

/-! ## 2. The fixed selector frame is the callee's native frame -/

/-! ## 3. The fixed selector table residual -/

end NearCubicWires.FixedSelectorProjectionTableStage
