import Proof.Wire_3_5.Primitive.ThresholdWriter.NumsPort
import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront2

/-! # THR: the THR port types with the empty tuple (`a' = 0`) included

P3:3068 (lem:primitive): "Fix a polynomial description envelope, a tuple arity at most four, and an accuracy exponent
`D>0`." Both THR writer targets quantify over `a' ≤ 4`, the empty tuple included. `NumsP.NumsPort` (W6 on ports) and
`TopFront2.TopFrontPort2` (the front end on ports) carry `1 ≤ a'`; their out-ports are defined for every `a'` (at
`a' = 0` the front end's circuit ports are blank and the numbers are `thrNumVals` of the empty tuple: `|𝒢| = |ThrEq|`,
`M = |occs|`, `B_* = a'·… = 0`, with `K = 8(|𝒢|+1)n^D ≥ 1` as before, `NumsP.den_pos`). This file restates both
without the lower bound:

* **`NumsPort2 alg Dexp`**: `NumsPort` for every `a' ≤ 4`; `NumsPort2.toV1`;
* **`TopFrontPort3 alg`**: `TopFrontPort2` for every `a' ≤ 4`; `TopFrontPort3.toV2`;
* `tf2Out_empty`: at `a' = 0` the front end's out-ports are its in-ports (no circuit, no payload, no native word).

Paper quantities of the main types: as `NumsPort` (`|𝒢|`, `K`, the cutoff, `Σp`, `τ₀`, the fixed hash's `M, A, B_*, J,
t, e, ℓ₀, p`) and `TopFrontPort2` (each circuit's retained top children and native word). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.PortsE
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimThrW.Joins NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.NumsP NearCubicWires.WireExponent3_5.PrimThrW.TopFront2

/-- **The THR front end on ports, every `a' ≤ 4`** (`TopFrontPort2` without `1 ≤ a'`). -/
structure TopFrontPort3 (alg : RepairRepresentation.DecompositionAlgorithm) where
  x : ℕ
  s : ℕ
  M : Machine (10 + x) s
  cost : ℕ → ℕ
  Cc : ℕ
  Dc : ℕ
  cost_poly : ∀ m, ValidatorPolynomialDomination.PolyBounded (cost m) m Cc Dc
  run : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (tl : List Bool) (V : ℕ),
    1 ≤ n → a' ≤ 4 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) → TF2Ok Cs codes V →
    ∃ J : Fin x → List Bool, (∀ j, (J j).length ≤ cost V) ∧
      Step M (cost V) (fun _ => 0)
        (Fin.addCases (m := 10) (n := x) (motive := fun _ => List Bool)
          (tf2InPorts (Data.reqW n true (ReqBridge.thrCodes Cs) codes tl) V) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 10) (n := x) (motive := fun _ => List Bool)
          (tf2OutPorts alg (Data.reqW n true (ReqBridge.thrCodes Cs) codes tl) V Cs) J)

end NearCubicWires.WireExponent3_5.PrimThrW.PortsE
