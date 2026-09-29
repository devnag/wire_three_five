import Proof.Wire_3_5.Lists.ListMachineRowRadixContract

/-! # C2 rows, part 26: the RADIX row's machine contract

The per-row contract of RADIX rows (a THR entry is FILTER row × RADIX row) in the seed's `c2` shape
:

* `Req`: the row description — the fixed count hash's list data `D` (P3:2604), the digit populations (occurrence
  count and corner labels per digit, P3:2598-2599), the prime `p`, the radix `b_0`, the state `s` — and the call
  width `n`;
* `input`: the computable row record `radRowRecC`;
* `pre`: the labels cover the corners, the list is nested, at least one digit, `s < p`, `n ≥ 1`, and the LOAD
  CONDITION: the row's explicit cost bound `(M+1)^{2τ₀} · 128 · (|record|+1)^2` is within the preprocessing class at
  `(n, B.kOf n, B.psiOf n)` (P3:2618-2620: "The `2^{O(L²)}` internal digit tuples in (row:radix) are expansion
  preprocessing");
* `ref`/`encode`: `radixExpr` over the computable prints (`radRefC`) and `exprWord`;
* `errSpec`: at EVERY assignment of the corner pool the reference takes the value `H_{g,p,s} =
  [Σ_d b_0^d(t_d^+ − t_d^−) ≡ s (mod p)]` at the reported digit counts (P3:2608-2618: "Precisely one digit tuple is
  active, even when it is incorrect").

**`radBlocks`**: the `ClassBlocks` of the contract; **`radCertified`**: `Certified radContract`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.BlockPlatform

/-- A RADIX row request. -/
structure RadReq where
  D : ListData
  digs : List Dig
  p : ℕ
  b0 : ℕ
  s : ℕ
  n : ℕ

/-- The admissible requests. -/
def RadReq.Pre (r : RadReq) : Prop :=
  DigsOk r.digs ∧ (∀ j i, r.D.inLevel (j + 1) i = true → r.D.inLevel j i = true) ∧ 1 ≤ r.digs.length ∧ r.s < r.p

/-! ## The word-function run -/

/-! ## The class blocks and the certificate -/


end NearCubicWires.WireExponent3_5.ListMachine.Row
