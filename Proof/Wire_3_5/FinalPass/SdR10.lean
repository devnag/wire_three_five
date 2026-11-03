import Lean
import Proof.Wire_3_5.FinalPass.SdR9
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdI1
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.FinalPass.SdI5
import Proof.Wire_3_5.FinalPass.SdI8
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.SdR3
import Proof.Wire_3_5.FinalPass.SdR5
import Proof.Wire_3_5.FinalPass.SdR8
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


/-! # S4 v2, part R10: the runs at SYM and THR calls at the v2 constants

S4 v1's `Sd` part 10 (`capNeed_ge`, `ptc_sym`, `ptc_thr`, `sym_run`, `thr_run`) re-instantiated in namespace `Sd.R`, where the width `Tf`, the sizes' polynomial `Xf`
(`ZX`, `KX`) and their lemmas are S4 v2's (parts R2, R3: `CallIndexR`'s exponents on `(l, fe)`, `c_r` in the
coefficients); the statements and proofs are v1's, so S4 v2's degrees depend on `(l, fe)` alone.

Paper quantity of the main type: as in v1 (P3:3044-3048, 3114-3115, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR)
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 SdEntry2 symCallOf thrCallOf thrWords thrNums)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem ptc_sym (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Seams.ptCount l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ =
      Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .sym n)) *
        (2 ^ dRow ((callInputs l F kclk coef A a ha).starParams n hs) *
          2 ^ dR ((callInputs l F kclk coef A a ha).starParams n hs) *
          ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs).Q) := by
  simp only [Seams.ptCount, Seams.ptCountOf, dif_pos hs]
  rw [StarParams.card_centers, ← StarParams.centerBits_sum, pow_add]
  unfold dRow
  ring

theorem ptc_thr (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    Seams.ptCount l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ =
      Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n)) *
        (2 ^ dRow ((callInputs l F kclk coef A a ha).starParams n hs) *
          2 ^ dR ((callInputs l F kclk coef A a ha).starParams n hs) *
          ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs).Q) := by
  simp only [Seams.ptCount, Seams.ptCountOf, dif_pos hs]
  rw [StarParams.card_centers, ← StarParams.centerBits_sum, pow_add]
  unfold dRow
  ring

variable {W5 : WalkBankProducer} (F5 : FiltSetupSpec5 W5) (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

/-- **S4's run at a SYM star call of the family.** -/
theorem sym_run (hS : SymSizeOK l F kclk coef A a ha E Csz Dsz) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (W : ℕ)
    (hW : Seams.ptCount l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ * Seams.vmax l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ < 2 ^ W)
    (σ : WState (gns E.nw E.nsc (twF l F F5 E Dsz Dtz)) (bnr E.nn E.nrs))
    (ent : SdEntry2 l F kclk coef A a ha (gLay E (twF l F F5 E Dsz Dtz)) ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ W σ) :
    ∃ τ : WState (gns E.nw E.nsc (twF l F F5 E Dsz Dtz)) (bnr E.nn E.nrs),
      Step (M4 l F F5 E Csz Dsz Ctz Dtz)
        (Seams.seedsShape (Seams.seedCount l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
          (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CtF l F E Csz Dsz Ctz Dtz) (DtF l F E Dsz Dtz) ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
          (Seams.ptCount l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (CpF l F E Csz Dsz Ctz Dtz * (n + 1) ^ DpF l F E Dsz Dtz)
          (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CoF l F F5 E Csz Dsz Ctz Dtz) (DoF l F F5 E Dsz Dtz) ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩))
        (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) σ).H (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) σ).A (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) τ).H (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) τ).A ∧
      τ.st (fsB tN) = frame (binary W (Seams.fpNum l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)) ∧ τ.st gD = σ.st gD ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have henv : ∀ X ∈ carriers, Carrier.WithinEnvelope 26 X := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := hcall.2.2.1
  have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
  have H := atoms_of l F kclk coef A a ha E Csz Dsz Ctz Dtz .sym n hs carriers henv hcar
  have hnF : n ≤ (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length := FpInLen.n_le_fpIn ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hQF := q_le_fpIn_sym l F kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  have hkh := kh_le_sym l F kclk coef A a ha n a' Cs carriers translation hs
  have hQ1 := le_trans Nat.one_le_two_pow hkh
  have hcapN : capNeed (Xf l F E Csz Dsz Ctz Dtz n) (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + E.nn ≤
      (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := cap_ok l F kclk coef A a ha E Csz Dsz Ctz Dtz ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hc1 := capNeed_ge (Xf l F E Csz Dsz Ctz Dtz n) (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length
  have hc0 : 10000 * (Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n) + 100 ≤
      (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := by omega
  have hTX : Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ ≤ Xf l F E Csz Dsz Ctz Dtz n := x_T l F kclk coef A a ha E Csz Dsz Ctz Dtz ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hT2 : n + 2 ≤ Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ := n2_le_Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  obtain ⟨-, -, -, -, -, hdRow, hdR, -, -, -⟩ := star_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hPn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  have hpc := prep_caps ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .sym n) (Xf l F E Csz Dsz Ctz Dtz n) H _ hc0
  have hov : 10000 * (Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n) + 1 +
      budOf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs) ((callInputs l F kclk coef A a ha).filterParams .sym n) (Seams.carLen carriers 0)
        (Seams.carLen carriers 1) + 1 + (bodyA (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) E.nn + 1) ≤
      PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CoF l F F5 E Csz Dsz Ctz Dtz) (DoF l F F5 E Dsz Dtz) ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ :=
    (ov_ok l F kclk coef A a ha F5 E Csz Dsz Ctz Dtz .sym n hs carriers henv hcar _ _ hQF hkh hnF).trans
      (s5_ge l F kclk coef A a ha _ _ ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
  have hle := fpNum_le l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hlt := fpNum_lt l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hsz := x_sfn l F kclk coef A a ha E Csz Dsz Ctz Dtz hS n hs ha' Cs carriers hcar hd
  have hV := x_vsym l F kclk coef A a ha E Csz Dsz Ctz Dtz n ha' Cs carriers hd hcar
  have hnum : Seams.fpNum l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ =
      NumDen.symNum ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs).eqv
        ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs).S Cs carriers
        ((callInputs l F kclk coef A a ha).filterParams .sym n) (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers) := by
    simp only [Seams.fpNum, NumDen.numOf, dif_pos hs]
  have hnums : (PrimAsm.Data.unaryList (List.ofFn (E.nums (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers)))).length ≤
      (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := by
    rw [ul_ofFn]
    have h1 := hsz.1
    unfold symSize at h1
    omega
  have hneed : E.need (symSize E (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers)) ≤ (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := by
    have := hsz.2.1; omega
  obtain ⟨τ, hst, hN, hD, hsh, hreg⟩ := run_symG E (twF l F F5 E Dsz Dtz) _ (winF l F F5 E Dsz Dtz)
    (woutF l F F5 E Dsz Dtz) (winF_ne l F F5 E Dsz Dtz) (Mw l F F5 E Csz Dsz Ctz Dtz) (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz)
    (budOf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs) ((callInputs l F kclk coef A a ha).filterParams .sym n) (Seams.carLen carriers 0) (Seams.carLen carriers 1))
    W (Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
    ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs) carriers hcar
    ((callInputs l F kclk coef A a ha).filterParams .sym n) σ
    (sym_w8 (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    (sym_w13 (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    (sym_ws (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    (sym_ns (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    ent.num (ent_lo E ent) (ent_hi E ent) (ent_W E ent (winF l F F5 E Dsz Dtz) (woutF l F F5 E Dsz Dtz))
    ent.heads ent.regs ent.cell
    (writer_run l F kclk coef A a ha F5 E Csz Dsz Ctz Dtz .sym n hs carriers henv hcar)
    (fun x => dl_call _ x) (fun x => dr_call _ x) hpc.1
    (qnum_of ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .sym n) (Xf l F E Csz Dsz Ctz Dtz n) H
      (List.ofFn ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers translation hs).S)
      (Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (Fintype.card (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed)
      (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz)
      (show dR ((callInputs l F kclk coef A a ha).starParams n hs) ≤ Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ by omega)
      (show dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ by omega)
      hTX hV (by rw [List.length_ofFn]; exact hQF) hnF (by omega))
    hpc.2.1 hpc.2.2.1 hpc.2.2.2
    (hHT_of ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .sym n) (Xf l F E Csz Dsz Ctz Dtz n) H _ hc0) hnums hneed
    (by have h := lt_of_le_of_lt hle hW; rw [hnum] at h; exact h) (by have h := hlt; rw [hnum] at h; exact h)
  refine ⟨τ, Step.enlarge hst ?_, by rw [hnum]; exact hN, hD, hsh, hreg⟩
  rw [ptc_sym l F kclk coef A a ha n a' ha' Cs carriers translation hcall hs]
  exact cost_gen ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .sym n) (Xf l F E Csz Dsz Ctz Dtz n) H _ E.nn _ _ _ _ _ _ _ _ hQ1
    hsz.2.2 hV hTX (tab_ok l F kclk coef A a ha E Csz Dsz Ctz Dtz ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (pt_ok l F E Csz Dsz Ctz Dtz n) hov

/-- **S4's run at a THR star call of the family.** -/
theorem thr_run (hT : ThrSizeOK l F kclk coef A a ha Ctz Dtz) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩) (W : ℕ)
    (hW : Seams.ptCount l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ * Seams.vmax l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ < 2 ^ W)
    (σ : WState (gns E.nw E.nsc (twF l F F5 E Dsz Dtz)) (bnr E.nn E.nrs))
    (ent : SdEntry2 l F kclk coef A a ha (gLay E (twF l F F5 E Dsz Dtz)) ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ W σ) :
    ∃ τ : WState (gns E.nw E.nsc (twF l F F5 E Dsz Dtz)) (bnr E.nn E.nrs),
      Step (M4 l F F5 E Csz Dsz Ctz Dtz)
        (Seams.seedsShape (Seams.seedCount l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩)
          (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CtF l F E Csz Dsz Ctz Dtz) (DtF l F E Dsz Dtz) ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩)
          (Seams.ptCount l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩) (CpF l F E Csz Dsz Ctz Dtz * (n + 1) ^ DpF l F E Dsz Dtz)
          (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CoF l F F5 E Csz Dsz Ctz Dtz) (DoF l F F5 E Dsz Dtz) ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩))
        (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) σ).H (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) σ).A (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) τ).H (wenc (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) τ).A ∧
      τ.st (fsB tN) = frame (binary W (Seams.fpNum l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩)) ∧ τ.st gD = σ.st gD ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have henv : ∀ X ∈ carriers, Carrier.WithinEnvelope 26 X := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := hcall.2.2.1
  have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
  have H := atoms_of l F kclk coef A a ha E Csz Dsz Ctz Dtz .thr n hs carriers henv hcar
  have hnF : n ≤ (fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length := FpInLen.n_le_fpIn ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hQF := q_le_fpIn_thr l F kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  have hkh := kh_le_thr l F kclk coef A a ha n a' Cs carriers translation hs
  have hQ1 := le_trans Nat.one_le_two_pow hkh
  have hcapN : capNeed (Xf l F E Csz Dsz Ctz Dtz n) (fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + E.nn ≤
      (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := cap_ok l F kclk coef A a ha E Csz Dsz Ctz Dtz ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hc1 := capNeed_ge (Xf l F E Csz Dsz Ctz Dtz n) (fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length
  have hc0 : 10000 * (Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n) + 100 ≤
      (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := by omega
  have hTX : Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ ≤ Xf l F E Csz Dsz Ctz Dtz n := x_T l F kclk coef A a ha E Csz Dsz Ctz Dtz ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hT2 : n + 2 ≤ Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ := n2_le_Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩
  obtain ⟨-, -, -, -, -, hdRow, hdR, -, -, -⟩ := star_le ((callInputs l F kclk coef A a ha).starParams n hs)
  have hPn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  have hpc := prep_caps ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Xf l F E Csz Dsz Ctz Dtz n) H _ hc0
  have hov : 10000 * (Xf l F E Csz Dsz Ctz Dtz n * Xf l F E Csz Dsz Ctz Dtz n) + 1 +
      budOf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs) ((callInputs l F kclk coef A a ha).filterParams .thr n) (Seams.carLen carriers 0)
        (Seams.carLen carriers 1) + 1 + (bodyA (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) E.nn + 1) ≤
      PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (CoF l F F5 E Csz Dsz Ctz Dtz) (DoF l F F5 E Dsz Dtz) ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ :=
    (ov_ok l F kclk coef A a ha F5 E Csz Dsz Ctz Dtz .thr n hs carriers henv hcar _ _ hQF hkh hnF).trans
      (s5_ge l F kclk coef A a ha _ _ ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩)
  have hle := fpNum_le l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hlt := fpNum_lt l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hsz := x_tfn l F kclk coef A a ha E Csz Dsz Ctz Dtz hT n hs ha' Cs carriers translation hcar hd
  have hV : Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg ×
      PrimeIndex (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤
      Xf l F E Csz Dsz Ctz Dtz n := by
    rw [Fintype.card_prod]; exact x_vthr l F kclk coef A a ha E Csz Dsz Ctz Dtz n hs ha' Cs hd
  have hnum : Seams.fpNum l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ =
      NumDen.thrNum ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
        ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs).eqv
        ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs).S Cs carriers
        ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (ListFast.listReportFast (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers translation).D) := by
    simp only [Seams.fpNum, NumDen.numOf, dif_pos hs]
    rfl
  have hnums : (PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers
      translation)))).length ≤ (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := by
    rw [ul_ofFn]
    have h1 := hsz.1
    unfold ThrPt.thrSize at h1
    omega
  have hneed : ThrPt.thrPtProg.need (ThrPt.thrSize (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers translation)) ≤
      (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz) := by
    have := hsz.2.1; omega
  obtain ⟨τ, hst, hN, hD, hsh, hreg⟩ := run_thrG E (twF l F F5 E Dsz Dtz) _ (winF l F F5 E Dsz Dtz)
    (woutF l F F5 E Dsz Dtz) (winF_ne l F F5 E Dsz Dtz) (Mw l F F5 E Csz Dsz Ctz Dtz) (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz)
    (budOf l F F5 E Csz Dsz Ctz Dtz ((callInputs l F kclk coef A a ha).starParams n hs) ((callInputs l F kclk coef A a ha).filterParams .thr n) (Seams.carLen carriers 0) (Seams.carLen carriers 1))
    W (Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩) (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers translation)
    (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
    ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs) carriers hcar
    ((callInputs l F kclk coef A a ha).filterParams .thr n) σ
    (thr_w8 (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    (thr_ws (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    (thr_ns (callInputs l F kclk coef A a ha) (gate0 l F).alg E ha' carriers translation σ Cs hs (ent_w E ent))
    ent.num (ent_lo E ent) (ent_hi E ent) (ent_W E ent (winF l F F5 E Dsz Dtz) (woutF l F F5 E Dsz Dtz))
    ent.heads ent.regs ent.cell
    (writer_run l F kclk coef A a ha F5 E Csz Dsz Ctz Dtz .thr n hs carriers henv hcar)
    (fun x => dl_call _ x) (fun x => dr_call _ x) hpc.1
    (qnum_of ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Xf l F E Csz Dsz Ctz Dtz n) H
      (List.ofFn ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers translation hs).S)
      (Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩) (Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg ×
        PrimeIndex (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))))
      (fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length (KcF l F E Csz Dsz Ctz Dtz * ((fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ DcF l F E Dsz Dtz)
      (show dR ((callInputs l F kclk coef A a ha).starParams n hs) ≤ Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ by omega)
      (show dRow ((callInputs l F kclk coef A a ha).starParams n hs) ≤ Tf l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩ by omega)
      hTX hV (by rw [List.length_ofFn]; exact hQF) hnF (by omega))
    hpc.2.1 hpc.2.2.1 hpc.2.2.2
    (hHT_of ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Xf l F E Csz Dsz Ctz Dtz n) H _ hc0) hnums hneed
    (by have h := lt_of_le_of_lt hle hW; rw [hnum] at h; exact h) (by have h := hlt; rw [hnum] at h; exact h)
  refine ⟨τ, Step.enlarge hst ?_, by rw [hnum]; exact hN, hD, hsh, hreg⟩
  rw [ptc_thr l F kclk coef A a ha n a' ha' Cs carriers translation hcall hs]
  exact cost_gen ((callInputs l F kclk coef A a ha).starParams n hs) carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (Xf l F E Csz Dsz Ctz Dtz n) H _ E.nn _ _ _ _ _ _ _ _ hQ1
    hsz.2.2 hV hTX (tab_ok l F kclk coef A a ha E Csz Dsz Ctz Dtz ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hcall⟩) (pt_ok l F E Csz Dsz Ctz Dtz n) hov

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R

end
