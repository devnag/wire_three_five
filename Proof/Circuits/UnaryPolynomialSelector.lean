import Proof.Foundations.ScheduledRecovery

/-!
# Fixed unary selector for the recovery envelope

The recovery schedule is not an existential search oracle.  This module gives
one fixed, oracle-free register program which scans the canonical polynomial
envelope and returns its least half-crossing.  The coefficient, degree, and
source onset are constants embedded in the program; the only runtime input is
the canonical unary encoding of the target length.

The implementation deliberately keeps both numeric and unary copies of each
loop accumulator.  Numeric copies form the published output, while unary
copies are the structural loop controls supported by the small register
machine.  No decoded crossing, local proof, or caller-selected schedule enters
the machine state.
-/

namespace NearCubicWires.UnaryPolynomialSelector

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialSchedule
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.ScheduledRecovery
open NearCubicWires.VerifiedLinker

/-! ## Fixed register ABI -/



/-! ## Pure bounded scan -/

/-! ## Unary encoding bounds -/

/-! ## Interpreter-checked arithmetic loops -/

/-! ## Exact structural comparison -/

/-! ## One complete candidate evaluation -/

/-! ## Exact scan transitions -/

/-! ## Complete first-crossing scan -/

/-! ## Uniform resource envelope -/

end NearCubicWires.UnaryPolynomialSelector
