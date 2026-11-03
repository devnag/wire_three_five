import Proof.Wire_3_5.FinalPass.Bridge1
import Proof.Wire_3_5.FinalPass.S5TNum4
import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Proof.Wire_3_5.FinalPass.SdI10Base
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12

/-! # The final pass's assembly: the parts on `finalPass_of3` (P3:3044-3048, 3170-3181)

The finish term's parts from the open producers (SYM size `hS`, #124; the core half `core : CoreHalfGen2`, PA2; the out
machine `outG : OutGen mOut`, X6), at the SYM words `Sw0` (the `symPtEval`) and S4's tables producers `F5`:

* **`Xf`**: S4 (`Sd.seedsWS2Of`) at the size polynomials (`symOK` from `hS`; `thrOK` from `ThrSz.thrSize_poly`); the
  parts below are generic in S4 `X` (S4's constants are rebased on `CallIndexR` in S4 v2);
* **`bTf`**: BridgeT at the rooms `mThrL l`, `mCore l`, `mOut + 1` and the halves' register need (`K0f`, `D0f`);
* **`frontF`**: the front from the THR half (`S5T.thrHalfGen`) and `core` at `bridgeExt`/`bridgeRoom`;
* **`oF`**, **`scF`**, **`eF`**, **`OF`**: the out machine on the idle room (`o` its first tape, the rest scratch);
* **`finalPassAsm`**: `finalPass_of_s6` at S6's deliverable `S6Out` for these parts: `∀ l, FinalPassLeaf l`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- The SYM words (the evaluator). -/
noncomputable abbrev Sw0 : SymWords := SymPtEval2.toWords PrimT.S3.symPtEval

section Sizes

end Sizes

section S4v1

end S4v1

section Parts

end Parts

end NearCubicWires.WireExponent3_5.FinalPass.Finish
