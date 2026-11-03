import Proof.Wire_3_5.FinalPass.CloseBase
import Proof.Wire_3_5.Foundations.OutMachineGenBase
import Proof.Wire_3_5.UnionMachine.SymSize2Base

/-!
# The final pass's closure join, step 2

`finalPassClose` with two more of its producers supplied by verified code: the out machine
(X6: `Out.Gen.outOfPhases` with phases `P4.ph4`, `P5.ph5` … m7) and the SYM size polynomial
(`SymSize.symSize_poly`). The producers still open, one binder each:

* `mCore`, `core`: the core half (the `coreGen` over the pool writers SA/SB/NW/SW);
* `h1`, `h2`, `h3`: S6's size bounds N1–N3 (`PrimAsm.S6Fit`);
* `hU`: the uniformity bundle at these parts (X6).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close2

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Close

end NearCubicWires.WireExponent3_5.FinalPass.Close2
