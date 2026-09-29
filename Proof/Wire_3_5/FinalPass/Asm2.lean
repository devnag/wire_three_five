import Proof.Wire_3_5.FinalPass.Asm1
import Proof.Wire_3_5.FinalPass.SdR12

/-! # The final pass's assembly at S4 v2 (P3:3044-3048, 3114-3115, 3170-3181)

**`XfR F5 hS`**: S4 v2 (`Sd.R.seedsWS2Of`, the exponents on `(l, fe)`) at the size polynomials, with its degrees by
`rfl` (**`XfR_Dt`**, **`XfR_Dp`**, **`XfR_Do`**, **`XfR_Dc`**: functions of `l` and `fe` only, since `DszOf hS l` and
`DtzOf l` are on `l`), and **`finalPassR`**: the finish term `finalPassAsm2` at S4 v2 from the open producers (the core
half, the out machine, S6's target and the uniformity bundle).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

section S4v2
variable {W5 : PrimT.WalkBank.WalkBankProducer} (F5 : PrimAsm.FiltSetup.FiltSetupSpec5 W5)
  (hS : ∀ l : Literals, ∃ Dsz : ℕ, ∀ F : GateFree l, ∃ Csz : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval Csz Dsz)

/-- **S4 v2** at the size polynomials. -/
noncomputable def XfR (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    SeedsWS2 l F kclk coef A a ha Sw0 :=
  Sd.R.seedsWS2Of l F kclk coef A a ha F5 PrimT.S3.symPtEval (CszOf hS l F) (DszOf hS l) (CtzOf l F) (DtzOf l)
    (symOK hS l F kclk coef A a ha) (thrOK l F kclk coef A a ha)

end S4v2

/-- **The finish term at S4 v2**: the final pass from the open producers. -/
noncomputable def finalPassR {W5 : PrimT.WalkBank.WalkBankProducer} (F5 : PrimAsm.FiltSetup.FiltSetupSpec5 W5)
    (hS : ∀ l : Literals, ∃ Dsz : ℕ, ∀ F : GateFree l, ∃ Csz : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval Csz Dsz)
    (mCore : Literals → ℕ) (core : Bank.CoreHalfGen2 Sw0 S5T.mThrL mCore) (mOut : ℕ) (outG : Bank.OutGen mOut)
    (s6 : Assembly.S6Target Sw0 (XfR F5 hS) (bTf mCore core mOut) (frontF (XfR F5 hS) mCore core mOut)
      (oF (XfR F5 hS) mCore core mOut) (scF (XfR F5 hS) mCore core mOut) (OF (XfR F5 hS) mCore core mOut outG))
    (hU : Assembly.S6Uni Sw0 (XfR F5 hS) (bTf mCore core mOut) (frontF (XfR F5 hS) mCore core mOut)
      (oF (XfR F5 hS) mCore core mOut) (scF (XfR F5 hS) mCore core mOut) (OF (XfR F5 hS) mCore core mOut outG)) :
    (l : Literals) → FinalPassLeaf l :=
  finalPassAsm2 (XfR F5 hS) mCore core mOut outG s6 hU

end NearCubicWires.WireExponent3_5.FinalPass.Finish
