import Proof.Wire_3_5.FinalPass.Close3
import Proof.Wire_3_5.FinalPass.CoreJ18

/-!
# The final pass's closure join, step 4

`finalPassClose3` with the core half supplied by verified code: `coreGenJ` over the four
pool writers in their relaxed forms (`CoreWritersJ l`: SA `S4WordsMAJ`, SB `S4WordsMBJ`, NW `NumsMJ`, SW `SymWordsMJ`;
, -MJ). The producers still open:

* `Wr`: the four pool writers at every literal instance;
* `hU`: the uniformity bundle at these parts (the output machine).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close4

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Close NearCubicWires.WireExponent3_5.FinalPass.Close2

/-- **The final pass from the four pool writers and the uniformity bundle.** -/
noncomputable def finalPassClose4 (Wr : ∀ l : Literals, Core.CoreWritersJ l)
    (hU : Assembly.S6Uni Sw0 (XfR F5c UnionMachine.SymSize.symSize_poly)
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut)
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut)
      (oF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut)
      (scF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut)
      (OF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut outG)) :
    FinalPassStage1.StageT :=
  Close3.finalPassClose3 (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) hU

end NearCubicWires.WireExponent3_5.FinalPass.Close4
