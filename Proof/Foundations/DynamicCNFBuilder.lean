import Proof.Foundations.CanonicalBinaryProgram

/-!
# Executable canonical CNF list builder

The SAT opcode accepts the canonical `Encodable` code of a list of clauses.
This module closes the low-level dynamic-list seam: one fixed oracle-free
register program consumes a zero-terminated stream of clause codes in reverse
order and constructs exactly that canonical outer-list code.  Tseitin clause
generation remains a separate stage; no semantic formula-builder callback is
hidden here.
-/

namespace NearCubicWires.DynamicCNFBuilder

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Verified handoff to the actual SAT opcode -/

end NearCubicWires.DynamicCNFBuilder
