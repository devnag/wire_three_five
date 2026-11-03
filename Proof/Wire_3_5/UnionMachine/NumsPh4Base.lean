import Proof.Wire_3_5.UnionMachine.NumsPh3Base

/-! # NW: phase (d)'s type v4 (`PhD'`) and the assembly's statement over it (types only)

`NumsPh3.PhD x` is unsatisfiable (X6): `DBank` pins only `rT`, `rE`, `rV`, while `Final` needs every register
`0` within `C·(T+v+1)^D`; and at `v = 0`, `max(2^e·v) 1 < 2^T` holds for every `e`, so clearing `rE` can exceed
`C·(T+v+1)^D`. (both amendments):

* **`DBank'`**: `DBank` and every register but `rT`, `rE`, `rV` zero (the assembly clears `rN`, `rM` before (d));
* **`PhD'`**: (d) from `DBank` plus that register hypothesis, the steps and the residue at `C·(T+e+v+1)^D`
  (`e = n − k ≤ |fpIn|`, still polynomial);
* **`NumsOfPhases' x l : PhC x l → PhA x l → PhB x l → PhD' x → NumsMJ l`**.

Paper quantity of the main types: the final pass's denominator `Den = max(2^e·V, 1)` in `T_f`-bit binary
(P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsPh4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2

variable (x : ℕ)

/-- **(d), v4**: the unary → binary writer at width `T` with the shift `e`, from `DBank` and the register hypothesis,
within `C·(T+e+v+1)^D` steps (plain constants). -/
structure PhD' where
  s : ℕ
  M : Machine (LNS x + 2 + LNR) s
  C : ℕ
  D : ℕ
  run : ∀ (cap T e v B : ℕ) (w : List Bool) (σ : St x), T + e + v + 2 ≤ cap → max (2 ^ e * v) 1 < 2 ^ T →
    NumsPh3.DBank x σ w T e v B → (∀ q, q ≠ rT → q ≠ rE → q ≠ rV → σ.val q = 0) →
      ∃ (τ : St x) (n : ℕ), n ≤ C * (T + e + v + 1) ^ D ∧
        Step M n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
        NumsPh3.Final x τ w T (max (2 ^ e * v) 1) (B + C * (T + e + v + 1) ^ D)

end NearCubicWires.WireExponent3_5.UnionMachine.NumsPh4
