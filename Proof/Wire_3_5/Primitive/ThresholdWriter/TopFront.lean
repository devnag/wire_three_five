import Proof.Wire_3_5.Primitive.Writers.ThrDataIface

/-! # THR, the THR front end on ports: `TopFrontPort`, each circuit's native word and top children

P3:2543-2551 (row:threshold-rows): the equations `L_g` are built from the children of each circuit's retained top gate,
produced by the decomposition algorithm (`ThresholdRows.children alg c`, the constructor's output
`exactListWord (children)`, P3:3071-3091 for the call's circuits). The THR numbers (W6, via proof 1's `PacketsMeta` loops
on `Request.topWord`/`Request.nativeWord`) and the mod-`p` core both start from these words, so the front end is one
port machine (`WalkBankProducer` style, docked by base `Block.focusedInto`):

* `payOf alg c = frame (natWord |supp(top c)| ++ exactListWord (children alg c))` (one circuit's `Request.topWord`
  block, `PacketsMeta.Setup.pay`);
* `tfInPorts w` (port `0` the framed request word, ports `1 … 8` blank), `tfOutPorts alg w Cs` (port `0` kept; port
  `1 + i` the payload of circuit `i < a'`, port `5 + i` its native word `thrWord (Cs i)`; blank for `i ≥ a'`);
* **`TopFrontPort alg`**: one machine on `9 + x` tapes; for every THR tuple (`1 ≤ a' ≤ 4`, descriptions within
  `(n+1)^26`, codes of at most `K` bits), carriers' codes and request tail, from the in-ports (scratch blank, heads `0`),
  within `cost (n + K)` steps, every head at `0`, the out-ports on ports `0 … 8`, residues bounded by the cost.

Paper quantities of the main type: the children of each circuit's retained top (row:threshold-rows) and the circuits'
native words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TopFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm

/-- **One circuit's top payload**: its retained top's support size, then its children's exact list word, framed. -/
def payOf (alg : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  frame (natWord c.top.support.card ++ exactListWord (RepairOrdinary.ThresholdRows.children alg c))

end NearCubicWires.WireExponent3_5.PrimThrW.TopFront
