import Proof.Wire_3_5.Lists.ListMachineRowPopContract

/-! # C2 rows, part 17: the POP row's machine contract

The per-row contract of POP rows in the seed's `c2` shape:

* `Req`: the row description — the amplified list `P`, its seed `e`, the population (sign, `L` occurrences, corner
  labels), the target state `s` — and the call width `n`;
* `input`: the computable row record `popRowRecC`;
* `pre`: the labels cover the corners, the base lists are nested, `n ≥ 1`, and the LOAD CONDITION: the row's explicit
  cost bound `2^t · 128 · (|record|+1)^3` is within the preprocessing class at `(n, k, Ψ) = (n, B.kOf n, B.psiOf n)`
  — the ledger's class arguments;
* `ref`/`encode`: the computable reference expression `popRefC` and `exprWord`;
* `errSpec`: at EVERY assignment of the corner pool the reference takes the value `[flatReport(Z^±) = s]` of the amplified list at the population point (P3:1519-1526).

**`popBlocks`**: the `ClassBlocks` of the contract (the POP row machine, all heads rewound by a masked reset from an
empty log); **`popCertified`**: `Certified popContract`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.BlockPlatform

/-- A POP row request. -/
structure PopReq where
  P : FlatListParams
  e : P.FlatSeed
  L : ℕ
  sgn : Bool
  labs : List ℕ
  s : Fin (P.M + 1)
  n : ℕ

/-! ## The word-function run -/

/-! ## The class blocks and the certificate -/


end NearCubicWires.WireExponent3_5.ListMachine.Row
