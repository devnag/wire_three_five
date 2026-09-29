import Proof.Wire_3_5.FinalPass.SdR11

/-! # S4 v2, part R12: S4's degrees on `(l, fe)` alone (the uniformity `S6Uni` needs)

S4 v2's exponents with the filter error degree `fe` explicit (**`ZTe l fe`**, **`ZXe l fe E Dsz Dtz`**) and, by `rfl`,
the degrees of `Sd.R.seedsWS2Of` through them: **`seedsWS2Of_Dt`** (`3·ZXe`), **`seedsWS2Of_Dp`** (`4·ZXe`),
**`seedsWS2Of_Do`** (`2·ZXe + budD (E2 F5 ZXe) ZXe ZXe Dc₂ + 3·ZXe`), **`seedsWS2Of_Dc`** (`3·ZXe`). With the size
polynomials' degrees on `l` (`Dsz`, `Dtz`), S4's degrees are fixed before the gate (P3:3114-3115).

Paper quantity of the main type: the seeds phase's powers of `n`, fixed before the gate (P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section U
variable (l : Literals) (fe : ℕ) (E : SymPtEval2) (Dsz Dtz : ℕ)

/-- The width's exponent at the filter error degree `fe`. -/
noncomputable def ZTe : ℕ :=
  PrimAsm.CallIndexR.gapZR l fe + PrimAsm.CallIndexR.symZI l fe + PrimAsm.CallIndexR.thrZI l fe + ZV l + 4

/-- **The sizes' exponent** at the filter error degree `fe`. -/
noncomputable def ZXe : ℕ :=
  52 + PrimAsm.CallIndexR.gapZR l fe + PrimAsm.CallIndexR.capZR l + ZV l + Dsz * (E.D + 1) +
    Dtz * (ThrPt.thrPtProg.D + 1) + ZTe l fe

end U

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
variable {W5 : WalkBankProducer} (F5 : FiltSetupSpec5 W5) (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

theorem ZT_eq : ZT l F = ZTe l F.filterErrDeg := rfl

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R
