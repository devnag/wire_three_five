import Proof.Wire_3_5.Primitive.SeedFix.TS4LBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base

/-! # T (#120, thrStage4U), part 16: **`thrStage4U : ∀ l, ThrStage4U l`**

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (the THR call's numbers, computed once per call), P3:3083-3086 (the named
carriers), P3:3425-3430 (the THR filter's cap `B_T`), P3:3071-3091 ("the preprocessing … runs in time polynomial in
`n`") and P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`"): at every call family of the gate, the v4 data
stage is PA's v2 stage plus `m3M` on `x3 = thrStageRoom (gate0 l F).alg` extra tapes; its time `cost3G` and W6's
capacity need `needT` are polynomial, the degrees fixed by the literals, the coefficients by `c_r`:

* `fuel_le` (the run's fuel within `cost3G`), **`run3G`** (`ThrDataStage4.run3` at the gate);
* **`stage4At`** (the family's `ThrDataStage4`, `x3 := W6.thrStageRoom (gate0 l F).alg`), `stage4At_x3`;
* **`thrStage4U : ∀ l, ThrData.ThrStage4U l`** (degree `max (DcG l) (NDeg l)`, coefficient `CcG l c_r + NCoef l c_r`).

Paper quantities of the main type: the data word `dataWord (hashNums … ++ thrCounts Cs carriers)`, its cost and W6's
capacity need, both polynomial. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer

variable (l : Literals)

theorem unary_len_left (a b : List ℕ) : (unaryList a).length ≤ (unaryList (a ++ b)).length := by
  rw [W6.unaryList_append, List.length_append]; omega

end NearCubicWires.WireExponent3_5.PrimT.TS4
