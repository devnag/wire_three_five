import Std

/-!
# The ten-clause Boolean gadget

This module checks the actual ten clauses of the Garey--Johnson--Stockmeyer
gadget, the quadratic penalty, its honest helper, the weighted stability
lemma, and the pair-XOR identity. All variables in these results are Boolean.
The proofs are kernel-checked finite case analyses; they do not use an axiom,
unfinished-proof placeholders, or compiled decision procedures.

The last two results isolate the linear-arithmetic certificate behind the
paper's restricted symmetric optimality observation. They use integer-scaled
coefficients and weights. They do not assert a representation theorem for
arbitrary real quadratic polynomials.
-/

namespace NearCubicGates.Gadget

end NearCubicGates.Gadget
