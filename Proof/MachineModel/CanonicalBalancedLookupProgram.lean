import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed random access into canonical balanced sequences

Structural compilers reuse finite runner tables.  Those tables are encoded with
`encodeBalancedList`, so random access must follow the canonical midpoint tree
without first expanding it to a linked spine.  This fixed oracle-free program
does exactly that.  Every live value is a subterm of the input or a decrement
of the public length/index, which gives an honest width bound by the encoded
request itself.
-/

namespace NearCubicWires.CanonicalBalancedLookupProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces

/-! ## Source-independent resource closure -/

end NearCubicWires.CanonicalBalancedLookupProgram
