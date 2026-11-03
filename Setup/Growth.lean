import CheckedPCPP.Composite
import CheckedPCPP.H2Poly
import WorkerArith.W4PrepHot

/-!
# SetupU half 2: the native width is logarithmic, so every polynomial in it is at most linear in `N`

The near-cubic-gates paper: "All guesses have a fixed polynomial bound in `q` and hence are `o(N)`". The native width
`q = width s g N` satisfies `2^q ≤ A (N+1)^m` (proof 1's `HierarchyNormalizedBounds.proof_bound`; `A, m` depend on the
clock), hence `q ≤ A + m (⌊log₂ (N+1)⌋ + 1)` (`width_log`). With `(L+1)^d ≤ d!·2^d·2^L` (`pow_le_two_pow`):
* `qpoly`: for every `d`, `(q+1)^d ≤ C (N+1)` — exponent `1` in `N`, whatever `d` and the clock;
* `qpoly_le`: for every `d, c`, eventually `c (q+1)^d ≤ N`;
* `gadgets_lin`: the gadget count `M = 2^{cl}` is at most `C (N+1)`;
* `hierarchyWord_lin`: the hierarchy word has length at most `C (N+1)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicGates.Close NearCubicGates.Close.Transfer
open NearCubicGates.Close.Worker (width gadgets)

end NearCubicGates.Close.Setup
