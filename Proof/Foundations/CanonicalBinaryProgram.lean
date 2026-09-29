import Proof.Foundations.PolynomialClock
import Proof.Foundations.VerifiedLinker

/-!
# Fixed register-machine primitives for canonical binary syntax

This module contains the interpreter lemmas shared by executable codecs and the
fixed exact test for constructor tag one.  Variable-length public data is the
balanced syntax from `CanonicalBalanced`; the former linked-list validator was
removed rather than retained as a second wire format.
-/

namespace NearCubicWires.CanonicalBinaryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Exact constructor-tag primitive -/

/-! ## Reusable exact interpreter steps -/

/-! ## Shared balanced-tree transducer ABI -/

/-! ## Fixed shape-preserving controller -/

end NearCubicWires.CanonicalBinaryProgram
