import Proof.Wire_3_5.FinalPass.SdR3

/-! # S4 v2, part R5: the tables writer at the v2 constants

S4 v1's `Sd` part 5 (the writer's widths `wD`, `wC`, `wDL`, `wCL`, `Mw`, `nUf`, `capWf`, `budOf`, `writer_run`) re-instantiated in namespace `Sd.R`, where the width `Tf`, the sizes' polynomial `Xf`
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

/-- The writer's shell constants. -/
noncomputable def wD : ℕ := TabW.E2 F5 (ZX l F E Dsz Dtz)
noncomputable def wC : ℕ := TabW.CW F5 (KX l F E Csz Ctz)
noncomputable def wDL : ℕ := ZX l F E Dsz Dtz
noncomputable def wCL : ℕ := 2 * KX l F E Csz Ctz

/-- **The tables writer** of the family. -/
noncomputable def Mw := TabW.tabM W5 F5 F.cr (wD l F F5 E Dsz Dtz) (wC l F F5 E Csz Ctz) (wDL l F E Dsz Dtz)
  (wCL l F E Csz Ctz)

/-- The writer's per-unit bound at a star call. -/
noncomputable def nUf (P : StarParams) : ℕ :=
  TabW.A2 F5 (KX l F E Csz Ctz) * (2 ^ PrimAsm.NumsX.mOf P + 1) ^ TabW.E2 F5 (ZX l F E Dsz Dtz)

/-- The writer's cell capacity at a star call. -/
noncomputable def capWf (P : StarParams) : ℕ :=
  TabW.A1 F5 (KX l F E Csz Ctz) * (2 ^ PrimAsm.NumsX.mOf P + 1) ^ TabW.E1 F5 (ZX l F E Dsz Dtz)

/-- **The writer's budget** at a star call (the shell's cost). -/
noncomputable def budOf (P : StarParams) (FP : GapParams) (L0 L1 : ℕ) : ℕ :=
  2 * PrimAsm.ShellT.shellCostG (TabW.reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) P.n
    (wD l F F5 E Dsz Dtz) (wC l F F5 E Csz Ctz) 1 64
    (PrimAsm.ThrData.thrDataStage2.cost 0 (TabW.noCs P.n) [] (UnaryCalc.value 1 64 P.n) (UnaryCalc.value 1 64 P.n)) 1 (F.cr + 18)
    (TabW.c2Of F.cr P.n) (PrimAsm.NumsX.mOf P) (wDL l F E Dsz Dtz) (wCL l F E Csz Ctz) (nUf l F F5 E Csz Dsz Ctz Dtz P) + 2

/-- **The tables writer's run** at every star call of the family. -/
theorem writer_run (m : Mode) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) (carriers : List (Carrier n))
    (henv : ∀ X ∈ carriers, Carrier.WithinEnvelope 26 X) (hcar : carriers.length ≤ 2) :
    PrimAsm.WriterIfaceJ.WriterRun (Mw l F F5 E Csz Dsz Ctz Dtz)
      (budOf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs)
        ((callInputs l F kclk coef A a ha).filterParams m n) (Seams.carLen carriers 0) (Seams.carLen carriers 1))
      (PrimAsm.ShellX.shellInX W5.x (wD l F F5 E Dsz Dtz) 1 1 (wDL l F E Dsz Dtz))
      (PrimAsm.ShellX.shellOutX W5.x (wD l F F5 E Dsz Dtz) 1 1 (wDL l F E Dsz Dtz))
      (TabW.reqT n ((callInputs l F kclk coef A a ha).filterParams m n).len
        ((callInputs l F kclk coef A a ha).filterParams m n).cap ((callInputs l F kclk coef A a ha).filterParams m n).errExp
        (Seams.carLen carriers 0) (Seams.carLen carriers 1)
        (Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams m n))))
      (TabW.tabWord ((callInputs l F kclk coef A a ha).filterParams m n) (Seams.carLen carriers 0)
        (Seams.carLen carriers 1) ++ [false]) := by
  have H := atoms_of l F kclk coef A a ha E Csz Dsz Ctz Dtz m n hs carriers henv hcar
  have hQ := n2_le_m ((callInputs l F kclk coef A a ha).starParams n hs)
  have hX : Xf l F E Csz Dsz Ctz Dtz n ≤
      KX l F E Csz Ctz * (2 ^ PrimAsm.NumsX.mOf ((callInputs l F kclk coef A a ha).starParams n hs) + 1) ^
        ZX l F E Dsz Dtz :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)
  have hK0 : 1 ≤ KX l F E Csz Ctz := by have := hKX l F E Csz Ctz; omega
  have hE0 : 1 ≤ ZX l F E Dsz Dtz := by unfold ZX; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := TabW.tab_hyps F5
    (PrimAsm.NumsX.mOf ((callInputs l F kclk coef A a ha).starParams n hs))
    ((callInputs l F kclk coef A a ha).filterParams m n) n (Seams.carLen carriers 0) (Seams.carLen carriers 1)
    (KX l F E Csz Ctz) (ZX l F E Dsz Dtz) hQ hK0 hE0 (H.len.trans hX) (H.cap.trans hX)
    ((show _ ≤ _ by have := H.err; omega).trans hX) ((H.cl 0).trans hX) ((H.cl 1).trans hX) (H.G.trans hX)
  exact TabW.tab_writer W5 F5 F.cr ((callInputs l F kclk coef A a ha).starParams n hs) rfl
    ((callInputs l F kclk coef A a ha).filterParams m n) (Seams.carLen carriers 0) (Seams.carLen carriers 1)
    (wD l F F5 E Dsz Dtz) (wC l F F5 E Csz Ctz) (wDL l F E Dsz Dtz) (wCL l F E Csz Ctz)
    (capWf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs))
    (nUf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs)) _
    h1 h2 h3 h4 (Ledger.one_le_rowBCap (gateCap l) m (Ledger.rowBr F.cr n) (gateSp l n) n) h5 h6 h7 h8 h9 h10 le_rfl

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R

