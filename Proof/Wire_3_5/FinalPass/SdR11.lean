import Lean
import Proof.Wire_3_5.FinalPass.SdR10
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdI1
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.FinalPass.SdR5
import Proof.Wire_3_5.FinalPass.SdR8
import Proof.Wire_3_5.FinalPass.SdR9
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdR10Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 v2, part R11: **`seedsWS2Of`** at the v2 constants

S4 v1's `Sd` part 11 (`seedsWS2Of : SeedsWS2`) re-instantiated in namespace `Sd.R`, where the width `Tf`, the sizes' polynomial `Xf`
(`ZX`, `KX`) and their lemmas are S4 v2's (parts R2, R3: `CallIndexR`'s exponents on `(l, fe)`, `c_r` in the
coefficients); the statements and proofs are v1's, so S4 v2's degrees depend on `(l, fe)` alone.

Paper quantity of the main type: as in v1 (P3:3044-3048, 3114-3115, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
variable {W5 : WalkBankProducer} (F5 : FiltSetupSpec5 W5) (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

/-- **S4 at the machine level** (the `SeedsWS2` instance of the family). -/
noncomputable def seedsWS2Of (hS : SymSizeOK l F kclk coef A a ha E Csz Dsz)
    (hT : ThrSizeOK l F kclk coef A a ha Ctz Dtz) : Seams.SeedsWS2 l F kclk coef A a ha E.toWords where
  L := gLay E (twF l F F5 E Dsz Dtz)
  s := _
  M := M4 l F F5 E Csz Dsz Ctz Dtz
  Kc := KcF l F E Csz Dsz Ctz Dtz
  Dc := DcF l F E Dsz Dtz
  tab := fun r => PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CtF l F E Csz Dsz Ctz Dtz) (DtF l F E Dsz Dtz) r
  pt := fun r => CpF l F E Csz Dsz Ctz Dtz * (r.1.n + 1) ^ DpF l F E Dsz Dtz
  ov := fun r => PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CoF l F F5 E Csz Dsz Ctz Dtz) (DoF l F F5 E Dsz Dtz) r
  Cp := CpF l F E Csz Dsz Ctz Dtz
  Dp := DpF l F E Dsz Dtz
  Ct := CtF l F E Csz Dsz Ctz Dtz
  Dt := DtF l F E Dsz Dtz
  Co := CoF l F F5 E Csz Dsz Ctz Dtz
  Do := DoF l F F5 E Dsz Dtz
  pt_le := fun _ => le_rfl
  tab_le := fun _ => le_rfl
  ov_le := fun _ => le_rfl
  run := fun r W hW σ ent => by
    have hlt := lt_of_le_of_lt (fpNum_le l F kclk coef A a ha r) hW
    obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
    cases mode with
    | sym =>
      obtain ⟨τ, hst, hN, hD, hsh, hreg⟩ :=
        sym_run l F kclk coef A a ha F5 E Csz Dsz Ctz Dtz hS n a' ha' Cs carriers translation hcall W hW σ ent
      exact ⟨τ, hst, hN, hD.trans ent.den, hsh, hreg, hlt⟩
    | thr =>
      obtain ⟨τ, hst, hN, hD, hsh, hreg⟩ :=
        thr_run l F kclk coef A a ha F5 E Csz Dsz Ctz Dtz hT n a' ha' Cs carriers translation hcall W hW σ ent
      exact ⟨τ, hst, hN, hD.trans ent.den, hsh, hreg, hlt⟩

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R

end
