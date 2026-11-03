import Lean
import Proof.Wire_3_5.FinalPass.Close2
import Proof.Wire_3_5.UnionMachine.S6Sizes
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Asm1
import Proof.Wire_3_5.FinalPass.Asm2
import Proof.Wire_3_5.FinalPass.S5TInst
import Proof.Wire_3_5.FinalPass.S6Iface
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.UnionMachine.SymSize2
import Proof.Wire_3_5.FinalPass.Close2Base
import Proof.Wire_3_5.UnionMachine.S6SizesBase


noncomputable section
set_option maxRecDepth 120000


/-!
# The final pass's closure join, step 3

`finalPassClose2` with S6's size bounds N1–N3 supplied by verified code (C6b:
`S6Sizes.fpIn_bound`, `seedCount_bound`, `ptCount_bound`). The producers still open, one binder each:

* `mCore`, `core`: the core half (the `coreGen` over the pool writers SA/SB/NW/SW);
* `hU`: the uniformity bundle at these parts (X6).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close3

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Close NearCubicWires.WireExponent3_5.FinalPass.Close2

/-- **The final pass from exactly its remaining open producers**: the core half and the uniformity bundle. -/
noncomputable def finalPassClose3
    (mCore : Literals → ℕ) (core : Bank.CoreHalfGen2 Sw0 S5T.mThrL mCore)
    (hU : Assembly.S6Uni Sw0 (XfR F5c UnionMachine.SymSize.symSize_poly) (bTf mCore core Out.mOut)
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut)
      (oF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut)
      (scF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut)
      (OF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut outG)) :
    FinalPassStage1.StageT :=
  finalPassClose2 mCore core UnionMachine.S6Sizes.fpIn_bound UnionMachine.S6Sizes.seedCount_bound
    UnionMachine.S6Sizes.ptCount_bound hU

end NearCubicWires.WireExponent3_5.FinalPass.Close3

end
