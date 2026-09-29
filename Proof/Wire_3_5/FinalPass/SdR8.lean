import Proof.Wire_3_5.FinalPass.SdR5

/-! # S4 v2, part R8: the seeds phase's constants at the v2 constants

S4 v1's `Sd` part 8 (`cXf`, `KcF`, `DcF`, `CtF`, `DtF`, `CpF`, `DpF`, `CoF`, `DoF`, `xf_le`, `pt_ok`, `tab_ok`, `cap_ok`) re-instantiated in namespace `Sd.R`, where the width `Tf`, the sizes' polynomial `Xf`
(`ZX`, `KX`) and their lemmas are S4 v2's (parts R2, R3: `CallIndexR`'s exponents on `(l, fe)`, `c_r` in the
coefficients); the statements and proofs are v1's, so S4 v2's degrees depend on `(l, fe)` alone.

Paper quantity of the main type: as in v1 (P3:3044-3048, 3114-3115, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL)
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

variable {W5 : WalkBankProducer} (F5 : FiltSetupSpec5 W5) (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

/-- The sizes' polynomial's coefficient at `n + 1`. -/
noncomputable def cXf : ℕ := KX l F E Csz Ctz * 2 ^ ZX l F E Dsz Dtz

/-- **The register capacity's constants.** -/
noncomputable def KcF : ℕ := 10000 * cXf l F E Csz Dsz Ctz Dtz ^ 3 + 106 + E.nn
noncomputable def DcF : ℕ := 3 * ZX l F E Dsz Dtz

/-- **The per-seed constants.** -/
noncomputable def CtF : ℕ := 100000 * cXf l F E Csz Dsz Ctz Dtz ^ 3
noncomputable def DtF : ℕ := 3 * ZX l F E Dsz Dtz

/-- **The per-point constants.** -/
noncomputable def CpF : ℕ := 23000 * cXf l F E Csz Dsz Ctz Dtz ^ 4
noncomputable def DpF : ℕ := 4 * ZX l F E Dsz Dtz

/-- **The overhead's constants.** -/
noncomputable def CoF : ℕ :=
  10000 * cXf l F E Csz Dsz Ctz Dtz ^ 2 +
    budC (wD l F F5 E Dsz Dtz) (wC l F F5 E Csz Ctz) (wDL l F E Dsz Dtz) (wCL l F E Csz Ctz) F.cr
      (cXf l F E Csz Dsz Ctz Dtz) PrimAsm.ThrData.thrDataStage2.Cc PrimAsm.ThrData.thrDataStage2.Dc +
    (2400 + 3 * E.nn) * (KcF l F E Csz Dsz Ctz Dtz + 1) + 3
noncomputable def DoF : ℕ :=
  2 * ZX l F E Dsz Dtz + budD (wD l F F5 E Dsz Dtz) (wDL l F E Dsz Dtz) (ZX l F E Dsz Dtz)
    PrimAsm.ThrData.thrDataStage2.Dc + DcF l F E Dsz Dtz

theorem xf_le (n m : ℕ) (h : n ≤ m) :
    Xf l F E Csz Dsz Ctz Dtz n ≤ cXf l F E Csz Dsz Ctz Dtz * (m + 1) ^ ZX l F E Dsz Dtz := by
  unfold Xf cXf
  rw [Nat.mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem pt_ok (n : ℕ) :
    23000 * (Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n *
      Xf l F E Csz Dsz Ctz Dtz n) ≤ CpF l F E Csz Dsz Ctz Dtz * (n + 1) ^ DpF l F E Dsz Dtz := by
  have h := xf_le l F E Csz Dsz Ctz Dtz n n le_rfl
  unfold CpF DpF
  calc _ ≤ 23000 * ((cXf l F E Csz Dsz Ctz Dtz * (n + 1) ^ ZX l F E Dsz Dtz) *
        (cXf l F E Csz Dsz Ctz Dtz * (n + 1) ^ ZX l F E Dsz Dtz) * (cXf l F E Csz Dsz Ctz Dtz * (n + 1) ^ ZX l F E Dsz Dtz) *
        (cXf l F E Csz Dsz Ctz Dtz * (n + 1) ^ ZX l F E Dsz Dtz)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h h) h) h)
    _ = _ := by ring

theorem tab_ok (r : FReq l F kclk coef A a ha) :
    100000 * (Xf l F E Csz Dsz Ctz Dtz r.1.n * Xf l F E Csz Dsz Ctz Dtz r.1.n * Xf l F E Csz Dsz Ctz Dtz r.1.n) ≤
      PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CtF l F E Csz Dsz Ctz Dtz) (DtF l F E Dsz Dtz) r := by
  have h := xf_le l F E Csz Dsz Ctz Dtz r.1.n _ (FpInLen.n_le_fpIn r)
  refine le_trans ?_ (s5_ge l F kclk coef A a ha _ _ r)
  unfold CtF DtF
  calc _ ≤ 100000 * ((cXf l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha r).length + 1) ^ ZX l F E Dsz Dtz) *
        (cXf l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha r).length + 1) ^ ZX l F E Dsz Dtz) *
        (cXf l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha r).length + 1) ^ ZX l F E Dsz Dtz)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul h h) h)
    _ = _ := by ring

theorem cap_ok (r : FReq l F kclk coef A a ha) :
    capNeed (Xf l F E Csz Dsz Ctz Dtz r.1.n) (fpIn l F kclk coef A a ha r).length + E.nn ≤
      KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha r).length + 1) ^ DcF l F E Dsz Dtz :=
  cap_poly _ _ _ _ _ (xf_le l F E Csz Dsz Ctz Dtz r.1.n _ (FpInLen.n_le_fpIn r)) (by unfold ZX; omega)

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R

