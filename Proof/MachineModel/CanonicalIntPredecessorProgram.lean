import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical integer predecessor

The public integer syntax is `pair(sign, encodeNat magnitude)`.  This module
implements predecessor with one fixed oracle-free program: a structural
adapter places the magnitude first, the canonical natural decoder produces a
native magnitude while preserving the sign, and a fixed final stage performs
the three integer cases before restoring canonical syntax.
-/

namespace NearCubicWires.CanonicalIntPredecessorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Native predecessor and canonical re-encoding -/

/-! ## One public linked program -/

end NearCubicWires.CanonicalIntPredecessorProgram
