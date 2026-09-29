import Proof.Circuits.CallableRelocation
import Proof.Circuits.CanonicalWitnessCodec
import Proof.MachineModel.CanonicalBitSerialModProgram
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram

/-!
# Total canonical-rational validation

A legal coefficient has one public representation: a two-cell tagged tuple
containing a canonical signed numerator and a positive canonical denominator.
This module validates that representation with one fixed interpreter pipeline.
Reducedness is decided by an executable Euclidean controller whose only
remainder implementation is the shared bit-serial modulo program.
-/

namespace NearCubicWires.CanonicalRationalValidationProgram

open NearCubicWires
open NearCubicWires.CallableRelocation
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-! ## Euclidean gcd with one relocated modulo implementation -/

def gcdCalleeRegisterBase : ℕ := 10

def gcdCalleeSpan : ℕ :=
  programRegisterSpan bitSerialModProgram

def gcdLoopPc : ℕ := 2

def gcdResetBase : ℕ := 3

def gcdPrepareBase : ℕ :=
  gcdResetBase + gcdCalleeSpan

def gcdCalleeBase : ℕ :=
  gcdPrepareBase + 4

def gcdReturnPc : ℕ :=
  gcdCalleeBase + bitSerialModProgram.length

def gcdSuccessPc : ℕ :=
  gcdReturnPc + 4

/-- Register ABI:

* `r1`: immutable public input length;
* `r2/r3`: current Euclidean pair;
* `r4`: paired modulo request;
* `r5`: relocated-call accumulator;
* `r6/r7`: remainder and zero scratch;
* `r10...`: isolated bit-serial modulo bank.
-/
def canonicalGcdPrefix : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 gcdLoopPc
  , .branchZero 3 gcdSuccessPc gcdResetBase
  ]

def canonicalGcdPrepareProgram : NPOracleProgram :=
  [ .pair 2 3 4 (gcdPrepareBase + 1)
  , .copy 4 gcdCalleeRegisterBase (gcdPrepareBase + 2)
  , .copy 1 (gcdCalleeRegisterBase + 1) (gcdPrepareBase + 3)
  , .set 5 0 gcdCalleeBase
  ]

@[simp] private theorem canonicalGcdPrefix_length :
    canonicalGcdPrefix.length = 3 := rfl

@[simp] private theorem canonicalGcdPrepareProgram_length :
    canonicalGcdPrepareProgram.length = 4 := rfl

/-! ## The polynomial charge of the Euclidean controller

Each Euclidean step charges one relocated bit-serial remainder, whose budget is
linear in the numerator's binary width.  What remains is the step count: a
remainder is at most half of its own dividend, so two steps at least halve the
second operand and the controller runs for at most `2 * natBitLength right + 2`
steps.  Neither factor contains an operand magnitude. -/

/-! ## Fixed rational-field projection and canonical Nat stages -/

/-! ## Unique total rational validator -/

end NearCubicWires.CanonicalRationalValidationProgram
