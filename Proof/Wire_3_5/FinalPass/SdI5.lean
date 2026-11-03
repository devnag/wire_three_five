import Lean
import Proof.Wire_3_5.FinalPass.SdI4
import Proof.Wire_3_5.FinalPass.FpInLenBase
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdI2
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdI5Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 (the seeds phase), part 54: the tables writer at a star call of the family (P3:2036-2101, 3170-3178)

The tables writer `TabW.tabM` at the constants `K₀ = KX`, `E₀ = ZX` (the sizes' polynomial read at the writer's
dimension `2^m + 1 ≥ n + 2`, `m = mOf P`): **`writer_run`**, its run (`TabW.tab_writer` with `TabW.tab_hyps`) at every
star call of the family, within the budget `budOf` (the writer shell's cost). The sample count against the input
(`q_le_fpIn_sym/thr`: `Q ≤ |fpIn|`) and the writer's dimension against the sample (`two_m_le`: `2^m ≤ Q²·(n+2)²`).

Paper quantity of the main type: the seeds' filter tables (`tabWord`, P3:2036-2101) on the writer's output. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
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

theorem q_le_fpIn_sym (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs).Q ≤
      (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length := by
  have h : ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers
      translation hs).Q ≤ (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
        ⟨n, .sym, a', ha', Cs, carriers, translation⟩).length := by
    simp only [seedWord, dif_pos hs]
    refine le_trans ?_ (FpInLen.length_le_sampleWord _ _)
    rw [List.length_ofFn]
    exact le_rfl
  refine le_trans h ?_
  unfold fpIn
  rw [List.length_append]
  exact Nat.le_add_left _ _

theorem q_le_fpIn_thr (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs).Q ≤
      (fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length := by
  have h : ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers
      translation hs).Q ≤ (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
        ⟨n, .thr, a', ha', Cs, carriers, translation⟩).length := by
    simp only [seedWord, dif_pos hs, List.length_append]
    refine le_trans ?_ (Nat.le_add_right _ _)
    refine le_trans ?_ (FpInLen.length_le_sampleWord _ _)
    rw [List.length_ofFn]
    exact le_rfl
  refine le_trans h ?_
  unfold fpIn
  rw [List.length_append]
  exact Nat.le_add_left _ _

theorem kh_le_sym (n a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤
      ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs).Q :=
  Sampler.N_le_sampleCount _ _ _ _ (by have := PrimAsm.CallIndex.n_ge_two l F hs; omega) (by omega)

theorem kh_le_thr (n a' : ℕ) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤
      ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs).Q :=
  Sampler.N_le_sampleCount _ _ _ _ (by have := PrimAsm.CallIndex.n_ge_two l F hs; omega) (by omega)

variable {W5 : WalkBankProducer} (F5 : FiltSetupSpec5 W5) (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

/-- The writer's shell constants. -/
noncomputable def wD : ℕ := TabW.E2 F5 (ZX l F E Dsz Dtz)
noncomputable def wC : ℕ := TabW.CW F5 (KX l F E Csz Ctz)
noncomputable def wDL : ℕ := ZX l F E Dsz Dtz
noncomputable def wCL : ℕ := 2 * KX l F E Csz Ctz

/-- **The tables writer** of the family. -/
noncomputable def Mw := TabW.tabM W5 F5 F.cr (wD l F F5 E Dsz Dtz) (wC l F F5 E Csz Ctz) (wDL l F E Dsz Dtz)
  (wCL l F E Csz Ctz)

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

end
