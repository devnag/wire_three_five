import Proof.Circuits.PaddedRunnerBudgetDomination
import Proof.Circuits.TotalInverseCanonicalCompiledBodyRun
import Proof.Circuits.TotalInverseCanonicalCompilerResources

/-! # Canonical structural-callee and range resources

This module freezes the six width consumers of the guarded structural atom
range.  The compiler-dependent callee width is separated exactly from the
same callee at compiler width zero; the remaining five range heads are kept at
their actual definitions.
-/

namespace NearCubicWires.TotalInverseCanonicalRangeResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.ValidatorPolynomialDomination

/-! ## 1. The compiler-dependent callee head -/

/-! ## 2. The exact six-way range -/

/-! ## 3. Polynomial closure of the range -/

end NearCubicWires.TotalInverseCanonicalRangeResources
