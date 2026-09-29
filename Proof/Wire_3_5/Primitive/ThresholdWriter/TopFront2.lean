import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront

/-! # THR, the THR front end on ports, v2: the capacity count is an in-port (`TopFrontPort2`)

P3:2543-2551 and P3:3071-3091, as `TopFront.TopFrontPort`. the request word carries the
carriers' codes and a tail of any length, and the verified request split (PA's `Data.setupW`) copies every
code into its slot, so its cost and its register capacity grow with the carriers' codes, which v1's `cost (n + K)`
does not see; and a machine that must fix its own register capacity from `n` alone needs an explicit polynomial bound
on the codes' bit lengths. v2 takes the capacity count from its caller, as PA's data stage does (`Data.rawIn … W`):

* `tf2InPorts w V` (port `0` the framed request, port `1` the count `1^V`, ports `2 … 9` blank), `tf2OutPorts alg w V Cs`
  (ports `0`, `1` kept; port `2 + i` circuit `i`'s payload `payOf`, port `6 + i` its native word; blank for `i ≥ a'`);
* **`TF2Ok n V Cs codes`**: the count dominates the split's needs at `L = (n+1)^26` (`Data.setup_spec`'s capacity
  hypotheses at capacity `2V + 2`: `n`, `a'`, the carriers' count, every circuit and carrier code's `natWord` plus
  `n + L`);
* **`TopFrontPort2 alg`**: one machine on `10 + x` tapes; from the in-ports under `TF2Ok`, within `cost V` (PolyBounded
  in `V`), every head at `0`, the out-ports, residues bounded by the cost.

Paper quantities of the main type: as v1 (each circuit's retained top children and native word). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TopFront2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront

/-- v2's in-ports: the framed request on `0`, the count `1^V` on `1`, the rest blank. -/
def tf2InPorts (w : List Bool) (V : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val = 0 then frame w else if i.val = 1 then List.replicate V true else []

/-- v2's out-ports: the inputs kept; circuit `i`'s payload on `2 + i`, its native word on `6 + i`. -/
def tf2OutPorts (alg : DecompositionAlgorithm) (w : List Bool) (V : ℕ) {q a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) : Fin 10 → List Bool := fun i =>
  if i.val = 0 then frame w else if i.val = 1 then List.replicate V true
  else if i.val < 6 then (if h : i.val - 2 < a' then payOf alg (Cs ⟨i.val - 2, h⟩) else [])
  else if h : i.val - 6 < a' then PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨i.val - 6, h⟩) else []

/-- **The count dominates the request split's needs** at `L = (n+1)^26` and capacity `2V + 2`. -/
structure TF2Ok {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (V : ℕ) : Prop where
  hk : codes.length ≤ 2
  hcN : natBitLength n + 1 ≤ 2 * V + 2
  hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2
  hcK : 2 ^ (natBitLength codes.length + 1) ≤ 2 * V + 2
  hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (natWord x).length + 2 + n + (n + 1) ^ 26 ≤ 2 * V + 2
  hcy : ∀ y ∈ codes, 2 * (natWord y).length + 2 + n + (n + 1) ^ 26 ≤ 2 * V + 2

end NearCubicWires.WireExponent3_5.PrimThrW.TopFront2
