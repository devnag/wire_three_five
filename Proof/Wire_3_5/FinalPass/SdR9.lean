import Proof.Wire_3_5.FinalPass.SdR8

/-! # S4 v2, part R9: the layout and the machine `M4` at the v2 constants

S4 v1's `Sd` part 9 (`twF`, `winF`, `woutF`, `M4`, `ov_ok`) re-instantiated in namespace `Sd.R`, where the width `Tf`, the sizes' polynomial `Xf`
(`ZX`, `KX`) and their lemmas are S4 v2's (parts R2, R3: `CallIndexR`'s exponents on `(l, fe)`, `c_r` in the
coefficients); the statements and proofs are v1's, so S4 v2's degrees depend on `(l, fe)` alone.

Paper quantity of the main type: as in v1 (P3:3044-3048, 3114-3115, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
variable {W5 : WalkBankProducer} (F5 : FiltSetupSpec5 W5) (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

/-- The tables writer's tape count. -/
noncomputable def twF : ℕ := PrimAsm.ShellX.STx W5.x (wD l F F5 E Dsz Dtz) 1 1 (wDL l F E Dsz Dtz) + 1

/-- The writer's input port. -/
noncomputable def winF : Fin (twF l F F5 E Dsz Dtz) :=
  PrimAsm.ShellX.shellInX W5.x (wD l F F5 E Dsz Dtz) 1 1 (wDL l F E Dsz Dtz)

/-- The writer's output port. -/
noncomputable def woutF : Fin (twF l F F5 E Dsz Dtz) :=
  PrimAsm.ShellX.shellOutX W5.x (wD l F F5 E Dsz Dtz) 1 1 (wDL l F E Dsz Dtz)

theorem winF_ne : winF l F F5 E Dsz Dtz ≠ woutF l F F5 E Dsz Dtz := PrimAsm.ShellX.shellInX_ne_out

/-- **The seeds phase's machine** of the family. -/
noncomputable def M4 :=
  s4M E (twF l F F5 E Dsz Dtz) _ (winF l F F5 E Dsz Dtz) (woutF l F F5 E Dsz Dtz) (Mw l F F5 E Csz Dsz Ctz Dtz)

/-- **The overhead at a star call.** -/
theorem ov_ok (m : Mode) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) (carriers : List (Carrier n))
    (henv : ∀ X ∈ carriers, Carrier.WithinEnvelope 26 X) (hcar : carriers.length ≤ 2) (Q Fn : ℕ) (hQF : Q ≤ Fn)
    (hkh : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤ Q) (hnF : n ≤ Fn) :
    10000 * (Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n) + 1 +
        budOf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs)
          ((callInputs l F kclk coef A a ha).filterParams m n) (Seams.carLen carriers 0) (Seams.carLen carriers 1) + 1 +
        (bodyA (KcF l F E Csz Dsz Ctz Dtz * (Fn + 1) ^ DcF l F E Dsz Dtz) E.nn + 1) ≤
      CoF l F F5 E Csz Dsz Ctz Dtz * (Fn + 1) ^ DoF l F F5 E Dsz Dtz := by
  have H := atoms_of l F kclk coef A a ha E Csz Dsz Ctz Dtz m n hs carriers henv hcar
  have hQ := n2_le_m ((callInputs l F kclk coef A a ha).starParams n hs)
  have hX : Xf l F E Csz Dsz Ctz Dtz n ≤
      KX l F E Csz Ctz * (2 ^ PrimAsm.NumsX.mOf ((callInputs l F kclk coef A a ha).starParams n hs) + 1) ^
        ZX l F E Dsz Dtz :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)
  have hK0 : 1 ≤ KX l F E Csz Ctz := by have := hKX l F E Csz Ctz; omega
  have hE0 : 1 ≤ ZX l F E Dsz Dtz := by unfold ZX; omega
  obtain ⟨-, -, h3, -⟩ := TabW.tab_hyps F5
    (PrimAsm.NumsX.mOf ((callInputs l F kclk coef A a ha).starParams n hs))
    ((callInputs l F kclk coef A a ha).filterParams m n) n (Seams.carLen carriers 0) (Seams.carLen carriers 1)
    (KX l F E Csz Ctz) (ZX l F E Dsz Dtz) hQ hK0 hE0 (H.len.trans hX) (H.cap.trans hX)
    ((show _ ≤ _ by have := H.err; omega).trans hX) ((H.cl 0).trans hX) ((H.cl 1).trans hX) (H.G.trans hX)
  have hw := TabW.reqT_le n ((callInputs l F kclk coef A a ha).filterParams m n).len
    ((callInputs l F kclk coef A a ha).filterParams m n).cap ((callInputs l F kclk coef A a ha).filterParams m n).errExp
    (Seams.carLen carriers 0) (Seams.carLen carriers 1)
    (Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams m n))) (Xf l F E Csz Dsz Ctz Dtz n)
    H.n2 H.len H.cap (by have := H.err; omega) (H.cl 0) (H.cl 1) H.G
  have hcc : PrimAsm.ThrData.thrDataStage2.cost 0 (TabW.noCs n) ([] : List (Carrier n)) (UnaryCalc.value 1 64 n)
      (UnaryCalc.value 1 64 n) ≤ PrimAsm.ThrData.thrDataStage2.Cc * (129 * (Fn + 1)) ^ PrimAsm.ThrData.thrDataStage2.Dc := by
    have hp := PrimAsm.ThrData.thrDataStage2.cost_le (TabW.noCs n) ([] : List (Carrier n)) (UnaryCalc.value 1 64 n)
      (UnaryCalc.value 1 64 n) 0 (by omega) (by simp) (fun i => i.elim0) (by simp) (fun i => i.elim0) (by simp)
      (by show 2 ≤ n + 64 * (n + 1) ^ 1; rw [pow_one]; omega)
    unfold ValidatorPolynomialDomination.PolyBounded at hp
    refine hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    show 0 + n + 64 * (n + 1) ^ 1 + 64 * (n + 1) ^ 1 + 1 ≤ 129 * (Fn + 1)
    rw [pow_one]; omega
  have hb := bud_poly _ n (wD l F F5 E Dsz Dtz) (wC l F F5 E Csz Ctz) _ F.cr
    (PrimAsm.NumsX.mOf ((callInputs l F kclk coef A a ha).starParams n hs)) (wDL l F E Dsz Dtz) (wCL l F E Csz Ctz)
    (nUf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs)) (Xf l F E Csz Dsz Ctz Dtz n) Fn Q
    (cXf l F E Csz Dsz Ctz Dtz) (ZX l F E Dsz Dtz) PrimAsm.ThrData.thrDataStage2.Cc PrimAsm.ThrData.thrDataStage2.Dc
    h3 hw (xf_le l F E Csz Dsz Ctz Dtz n Fn hnF) hnF hcc
    (two_m_le ((callInputs l F kclk coef A a ha).starParams n hs) Q hkh) hQF
  exact ov_poly _ _ _ (Xf l F E Csz Dsz Ctz Dtz n) Fn (cXf l F E Csz Dsz Ctz Dtz) (ZX l F E Dsz Dtz) _ _ _
    (KcF l F E Csz Dsz Ctz Dtz) (DcF l F E Dsz Dtz) E.nn le_rfl (xf_le l F E Csz Dsz Ctz Dtz n Fn hnF) hb
    (bodyA_le _ _) rfl

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R

