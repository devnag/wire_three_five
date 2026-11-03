import Lean
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.UnionMachine.NumsPh4Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW: phase (d)'s type v4 (`PhD'`) and the assembly's statement over it (types only)

`NumsPh3.PhD x` is unsatisfiable (X6): `DBank` pins only `rT`, `rE`, `rV`, while `Final` needs every register
`0` within `C·(T+v+1)^D`; and at `v = 0`, `max(2^e·v) 1 < 2^T` holds for every `e`, so clearing `rE` can exceed
`C·(T+v+1)^D`. The amended statements:

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

/-- **NW's assembly over (d) v4**: the four phases give the `NumsMJ l`. -/
abbrev NumsOfPhases' (l : Literals) : Type :=
  NumsPh3.PhC x l → NumsPh3.PhA x l → NumsPh3.PhB x l → PhD' x → NumsMJ l

end NearCubicWires.WireExponent3_5.UnionMachine.NumsPh4

end
