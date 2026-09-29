import Proof.Foundations.CanonicalBinaryProgram

/-!
# Canonical binary arithmetic semantics

Arithmetic is stated over decoded little-endian bit streams, independently of
their balanced public tree representation.  Executable consumers traverse the
tree with the shared shape-preserving ABI in `CanonicalBinaryProgram`; this
module deliberately does not retain the obsolete linked-list comparator.
-/

namespace NearCubicWires.CanonicalBinaryArithmeticProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## Pure comparison semantics -/

/-! ## Fixed native-natural comparison

Resource counters and trusted public limits are native register values.  This
loop compares them in time linear in their binary width: it shifts both
operands right, retaining the order selected by the highest unequal bit seen
so far.  It does not convert either operand to unary and uses no SAT call.
-/

end NearCubicWires.CanonicalBinaryArithmeticProgram
