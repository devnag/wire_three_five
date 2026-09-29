import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface

/-! # PA (d), v2: the FILTER-setup interface with the request's head at `0`

`CellState.HashReqSpec` (C6's consumer) needs the request stream's head at `0` after the setup; `FiltSetupSpec`
states only the request's content. v2 adds the head, at entry and at exit:

* **`FsIn2`** = `FsIn` plus `σ.sh (sk x 0) = 0`; **`FiltSetupSpec2 W`**: `FiltSetupSpec`'s fields with the run from
  `FsIn2` also concluding `τ.sh (sk W.x 0) = 0`;
* the twin **`fsIn2_fsBank`** (`fsBank`, whose request head is `blankCell`'s `0`, meets `FsIn2`).

Paper quantities of the main type: as `FiltSetupSpec` (the regular filter's parameters and seed, the row's labels). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe (sk_ne)

/-- **The FILTER setup's entry bank, v2**: `FsIn` with the request's head at `0`. -/
structure FsIn2 (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (len cap err g r4 G off L : ℕ) : Prop extends FsIn x σ w out j u len cap err g r4 G off L where
  h0 : σ.sh (sk x 0) = 0

end NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup
