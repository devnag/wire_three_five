import Statement

/-!
# The paper's theorems, as propositions

This module defines propositions; `MainStatement` is the paper's main theorem, proved in `MainTheorem.lean` from the
nine published inputs. The others are not proved in this repository. The `E^NP` predicate uses the finite-control
multitape execution semantics, including a polynomial-time verifier for the oracle. The size measure is the top
multiplicity `W`, not the total number of wires.
-/

set_option autoImplicit false

namespace NearCubicGates.Target

open scoped BigOperators
open NearCubicWires

def lambda (n : ℕ) : ℕ := Nat.clog 2 n
def mu (n : ℕ) : ℕ := Nat.clog 2 (lambda n)

end NearCubicGates.Target
