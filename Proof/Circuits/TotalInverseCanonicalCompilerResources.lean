import Proof.Circuits.TotalInverseCanonicalCompilerRuns
import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.TotalInverseCanonicalCompilerResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalSelectiveCountCasesProgram
open NearCubicWires.ValidatorPolynomialDomination

/-! ## 1. Definition-level census

The outer total compiler has exactly two resource heads.  Width is the maximum
of the request-code width and the recursive candidate walk.  Fuel is the
seventeen-instruction parser plus that same recursive walk.  The definitions
below expose those two heads at the exact canonical target-indexed runner. -/

end NearCubicWires.TotalInverseCanonicalCompilerResources
