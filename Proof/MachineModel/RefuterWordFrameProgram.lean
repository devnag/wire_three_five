import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalNativeCallProgram

/-!
# The refuter-word frame

Every scheduled recovery stage below the branch dispatcher consumes the frame
`pair (encodeBitInput word) (pair sourceLength pointCode)`, where `word` is the
published refuter's own output at the scheduled source length.  This module is
the single fixed program that builds that frame from the requested point code
alone.

Three fixed stages, one imported call:

* a six-instruction prelude that emits the canonical `RefuterRequest` code
  beside the retained `(sourceLength, pointCode)` context;
* the shared context-preserving native caller applied once to the published
  refuter's own runner program;
* a six-instruction reframing adapter followed by the shared low-bit
  normalizer, which truncates the refuter's opaque output code to exactly the
  `sourceLength` bits read by `ExecutableSATOracleRefuter.output`.

The machine enters only through the numeral
`ExecutableWeakNondeterministicMachine.description`, which is the sole
machine-dependent register of the refuter request; this is exactly the
dependence isolated by
`CanonicalTargetLanguageProgram.inverseRefuterInput_eq_of_description`.
-/

namespace NearCubicWires.RefuterWordFrameProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The request prelude

Input `pointCode`, output
`pair (pair description sourceLength) (pair sourceLength pointCode)`.  The two
numerals are immediates of the instruction stream: the description is the only
machine-dependent one. -/

/-! ## 2. The truncation adapter

Input `pair outputCode (pair sourceLength pointCode)`, output
`pair (pair sourceLength outputCode) (pair sourceLength pointCode)`.  The left
component is precisely `bitInputPrefixInput sourceLength outputCode`. -/

/-! ## 3. The composed frame builder -/

end NearCubicWires.RefuterWordFrameProgram
