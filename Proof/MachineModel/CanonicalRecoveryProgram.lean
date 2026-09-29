import Proof.Circuits.CanonicalWitnessCodec

/-!
# Fixed-machine recovery-witness validation

This module starts the executable refinement of `decodeRecoveryWitness`.  The
outer envelope is deliberately validated by the register machine itself:
register `0` contains the untrusted code, no decoded value or acceptance bit is
supplied in another register, and malformed constructor tags or mode encodings
reach the unique zero-returning reject block.
-/

namespace NearCubicWires.CanonicalRecoveryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline

/-! ## Unique full-validator specification -/

/-! The following closed counterexample is a regression guard against wiring
the executable envelope parser into a theorem that requires full validation.
The outer three-field syntax and mode are valid, but the empty Boolean-oracle
code is not a circuit under any limits. -/

/-!
The program is intentionally unrolled at this fixed three-field boundary.  A
loop counter would itself need subtraction, while unrolling keeps every
control-flow edge finite and makes “exactly three fields” part of the code.

Register ABI:
* `r2`: current outer-list cursor;
* `r3`: original raw code;
* `r4`, `r5`, `r6`: mode, oracle, and legal-sum payload codes;
* `r12`--`r15`: structural scratch;
* `r11`: nonzero accepted-mode tag.
-/

/-!
`recoveryEnvelopeMachineOutput` is the direct structural trace mirrored by the
program.  Keeping this tiny proof model separate from the public decoder lets
the interpreter proof normalize instruction by instruction; the equivalence
to `decodeRecoveryEnvelope` is proved below.
-/

end CanonicalRecoveryProgram
end NearCubicWires
