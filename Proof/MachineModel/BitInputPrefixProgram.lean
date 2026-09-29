import Proof.Foundations.CanonicalBinaryProgram

/-!
# Canonical low-bit input projection

Imported evaluators receive the canonical code of their exact input arity.
When a recovered core is padded to a larger public arity, passing the public
code verbatim would leave unconstrained high bits in that evaluator ABI.  This
fixed oracle-free program computes `value % 2 ^ width`; it is the single input
normalizer shared by both recovery branches.
-/

namespace NearCubicWires.BitInputPrefixProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

end NearCubicWires.BitInputPrefixProgram
