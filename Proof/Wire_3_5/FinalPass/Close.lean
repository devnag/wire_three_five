import Lean
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.FinalPass.Asm2
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.Primitive.Writers.S6Fit
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.WalkStage
import Proof.Wire_3_5.Foundations.OutMachineP3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Asm1
import Proof.Wire_3_5.FinalPass.S5TInst
import Proof.Wire_3_5.FinalPass.S6Iface
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineIface
import Proof.Wire_3_5.FinalPass.CloseBase


noncomputable section
set_option maxRecDepth 120000


/-!
# The final pass's closure join

The finalpass leaf's finish term, stated from the producers given as binders, with every other
argument supplied by verified code: the FILTER setup `fsSpec walkBank` (C6, union-machine), the out machine's phases
`ph1`/`ph2`/`ph3` (X6/m4) and `ph6`, and S6's target `s6Target` (PA2). The open
producers, one binder each:

* `hS`: the SYM size polynomial (C6b);
* `mCore`, `core`: the core half (the `coreGen` over the pool writers SA/SB/NW/SW);
* `ph4`, `ph5`, `outOf`: the out machine's exact divisions, print and assembly (X6);
* `h1`, `h2`, `h3`: S6's size bounds N1–N3 (C6b, `PrimAsm.S6Fit`);
* `hU`: the uniformity bundle at these parts (the assembly).

The finish instantiates `finalPassClose` at the producers once they are verified, so the final join is already
checked. Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive`
(P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- **The final pass from exactly its open producers.** -/
noncomputable def finalPassClose
    (hS : ∀ l : Literals, ∃ Dsz : ℕ, ∀ F : GateFree l, ∃ Csz : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval Csz Dsz)
    (mCore : Literals → ℕ) (core : Bank.CoreHalfGen2 Sw0 S5T.mThrL mCore)
    (ph4 : Out.Ph4) (ph5 : Out.Ph5) (outOf : Out.OutOfPhases)
    (h1 : ∀ l, PrimAsm.S6Fit.FpInBound l) (h2 : ∀ l, PrimAsm.S6Fit.SeedCountBound l)
    (h3 : ∀ l, PrimAsm.S6Fit.PtCountBound l)
    (hU : Assembly.S6Uni Sw0 (XfR F5c hS) (bTf mCore core Out.mOut) (frontF (XfR F5c hS) mCore core Out.mOut)
      (oF (XfR F5c hS) mCore core Out.mOut) (scF (XfR F5c hS) mCore core Out.mOut)
      (OF (XfR F5c hS) mCore core Out.mOut (outOf Out.P1.ph1 Out.P2.ph2 Out.P3.ph3 ph4 ph5 Out.ph6))) :
    FinalPassStage1.StageT :=
  finalPassR F5c hS mCore core Out.mOut (outOf Out.P1.ph1 Out.P2.ph2 Out.P3.ph3 ph4 ph5 Out.ph6)
    (PrimAsm.S6Fit.s6Target _ _ _ _ _ _ _ h1 h2 h3) hU

end NearCubicWires.WireExponent3_5.FinalPass.Close

end
