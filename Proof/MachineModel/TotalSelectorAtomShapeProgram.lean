import Proof.Circuits.SelectorDrivenAtomContextRuns
import Proof.Circuits.TotalInverseCompilerRuns

/-!
# The guarded atom-count shape stage at the selector frame

The selector adapter computes the structural atom count at index `0`.  This
module rebuilds only that count tail around the total compiler and preserves
the existing selector context and frame contracts.
-/

namespace NearCubicWires.TotalSelectorAtomShapeProgram

open NearCubicWires
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.TotalStructuralAtomCalleeProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The count projection with compiler ownership exposed -/

/-! ## 2. The guarded count-and-pair stage -/

/-! ## 3. The selector-frame shape supplier -/

end NearCubicWires.TotalSelectorAtomShapeProgram
