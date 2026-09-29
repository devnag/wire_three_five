import Proof.Wire_3_5.FinalPass.Close
import Proof.Wire_3_5.Foundations.OutMachineGen
import Proof.Wire_3_5.UnionMachine.SymSize2

/-!
# The final pass's closure join, step 2

`finalPassClose` with two more of its producers supplied by verified code: the out machine
(the output machine: `Out.Gen.outOfPhases` with phases `P4.ph4`, `P5.ph5`, … m7) and the SYM size polynomial
(`SymSize.symSize_poly`). The producers still open, one binder each:

* `mCore`, `core`: the core half (`coreGen` over the pool writers SA/SB/NW/SW, -M);
* `h1`, `h2`, `h3`: S6's size bounds N1–N3 (`PrimAsm.S6Fit`);
* `hU`: the uniformity bundle at these parts (the output machine).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close2

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Close

/-- The out machine at its verified phases (the output machine). -/
noncomputable abbrev outG : Bank.OutGen Out.mOut :=
  Out.Gen.outOfPhases Out.P1.ph1 Out.P2.ph2 Out.P3.ph3 Out.P4.ph4 Out.P5.ph5 Out.ph6

/-- **The final pass from exactly its remaining open producers.** -/
noncomputable def finalPassClose2
    (mCore : Literals → ℕ) (core : Bank.CoreHalfGen2 Sw0 S5T.mThrL mCore)
    (h1 : ∀ l, PrimAsm.S6Fit.FpInBound l) (h2 : ∀ l, PrimAsm.S6Fit.SeedCountBound l)
    (h3 : ∀ l, PrimAsm.S6Fit.PtCountBound l)
    (hU : Assembly.S6Uni Sw0 (XfR F5c UnionMachine.SymSize.symSize_poly) (bTf mCore core Out.mOut)
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut)
      (oF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut)
      (scF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut)
      (OF (XfR F5c UnionMachine.SymSize.symSize_poly) mCore core Out.mOut outG)) :
    FinalPassStage1.StageT :=
  finalPassClose UnionMachine.SymSize.symSize_poly mCore core Out.P4.ph4 Out.P5.ph5 Out.Gen.outOfPhases h1 h2 h3 hU

end NearCubicWires.WireExponent3_5.FinalPass.Close2
