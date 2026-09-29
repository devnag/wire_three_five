import Proof.Wire_3_5.Primitive.Writers.ThrS3
import Proof.Wire_3_5.Primitive.Writers.ThrStage2

/-! # c4 THR block, the THR stage at capacity v2

The twin of `thrStageM`/`thrStage_run` on the setup at capacity v2 (`setupT3`): the wrapper, the decision loop
of a child family of the shape, the THR finisher; the stage ends with `sampleWord kh (seedPairs P s) ++ hbF` on port `2`.
* `thrStageM3`, **`thrStage3_run`**.

Paper quantity of the main type: the THR stage's output, the fixed seed's samples then the hash bits (P3:2932-2937,
3011-3016, 3034-3038, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (L : Lay)

/-- **The THR stage's machine.** -/
noncomputable def thrStageM3 (CL Cd Cc x3 s3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3)
    (P : WM (LNS 0) LNR) (F : C4Loop.ChildFam) (pd : ℕ) (hT : F.T + 1 + 1 + 1 ≤ L.T) :=
  C4Wrap.wrapM (setupT3 L CL Cd Cc x3 s3 M3 P) F L.oLP (hoffLb L x3 F hT) (liftX (hxb L x3) (C4SymW.symExt L pd))
    ThrFin.finM (offT L x3) (hoffT L x3) (ThrFin.extF L (hxb L x3) (hbT L x3))

/-- **The THR stage from its setup.** -/
theorem thrStage3_run (hDL : 16 ≤ L.D) (CL Cd Cc n : ℕ) (w sfx v : List Bool)
    (hw : w = RepairRepresentation.natWord n ++ sfx)
    (x3 s3 n3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3)
    (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ) (J : Fin x3 → List Bool)
    (h3 : Step M3 n3 (fun _ => 0)
      (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
        (Fin.addCases (Data.rawIn w n (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n))
          (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
      (fun _ => 0)
      (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J))
    (cs : List ℕ) (hO : tout (sTape Data.sOUT) = Data.dataWord cs) (hI : tout (sTape Data.sIN) = frame w)
    (τh : WState (LNS 0) LNR) (ch : ℕ)
    (hxe : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) ThrHB.hbXW (CellLoopD.blankCellD 0 w [] 0 []) τh ch)
    (hτh0 : τh.st (sk 0 0) = frame w) (hbF : List Bool) (hZ : τh.st ThrHB.sZ = marks hbF)
    (Pr : WM (LNS 0) LNR) (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) Pr (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)
    (hτ : ∀ j, τ.st (sk 0 (symO j)) = symClean Q kh ell cnt d2 fr dd j)
    (h Q' mm pr ρ : ℕ) (hell : 1 ≤ ell)
    (h31 : symClean Q kh ell cnt d2 fr dd 31 = List.replicate ell true)
    (h32 : symClean Q kh ell cnt d2 fr dd 32 = List.replicate ell true)
    (h33 : symClean Q kh ell cnt d2 fr dd 33 = List.replicate h true)
    (h34 : symClean Q kh ell cnt d2 fr dd 34 = List.replicate Q' true)
    (h35 : symClean Q kh ell cnt d2 fr dd 35 = List.replicate mm true)
    (h36 : symClean Q kh ell cnt d2 fr dd 36 = List.replicate pr true)
    (h37 : symClean Q kh ell cnt d2 fr dd 37 = NumsX.srcWord d2)
    (h38 : symClean Q kh ell cnt d2 fr dd 38 = NumsX.srcWord ρ) (B3 : ℕ) (pre post : List Bool)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w h Q' mm pr
      pre post)
    (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT q uu : ℕ)
    (hS : C4SymW.ChShape F pd P ents TWd Cap nT pre post q uu)
    (hL : ThrLinks P ents TWd Cap nT q uu v Q kh ell cnt d2 fr dd)
    (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS) (hR : F.cellCost + 1 ≤ 2 ^ ρ) (hkh : 1 ≤ P.kh)
    (s : Fin (8 * P.ell) → Bool) (hG : SeedFix.greedyLoop F.bound F.Rv = List.ofFn s) (Bd : ℕ)
    (hBd : C4Wrap.wrapCost (setupT3Cost L w n CL Cd Cc n3 (2 ^ C4Cap.capExp2 Cc n) ch (Data.unaryList cs) c ell d2 ρ B3)
      F (2 ^ ρ) (ThrFin.finCost P s hbF) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run ⟨thrXb L x3, _, thrStageM3 L CL Cd Cc x3 s3 M3 Pr F pd hT⟩ Bd w v
      (FinalPass.Sample.sampleWord P.kh (C4Iface.seedPairs P s) ++ hbF) := by
  obtain ⟨B', h0, fP0, fP1, fP2, fW, fMA, fMB, fUU, fRR, fPRE, fPOST, fLG, fmask, fbl, fhb, fbl2⟩ :=
    setupT3_run L hDL CL Cd Cc n w sfx v hw x3 s3 n3 M3 tout m J h3 cs hO hI τh ch hxe hτh0 hbF hZ Pr τ c hx hτ0
      (symClean Q kh ell cnt d2 fr dd) hτ ell h Q' mm pr d2 ρ hell h31 h32 h33 h34 h35 h36 h37 h38 B3 pre post hc3
  have hB : C4SymW.SymBank L pd P ents TWd Cap nT pre post q uu (fun i => B' (liftE (hxb L x3) i)) ρ v Q kh ell cnt d2
      fr dd :=
    ⟨fW, fP1, fMA, fUU, fRR, fPRE, fPOST, fLG, fmask, hL.e_ell, hL.e_kh, hL.e_Q, hL.e_ellQ, hL.e_TW, hL.e_Cap, hL.e_q,
      hL.e_dd, hL.e_cnt, hL.e_mod, hL.e_uu, hL.e_v, hL.h_ell1⟩
  exact thrLay_run L x3 F pd P ents TWd Cap nT pre post q uu ρ v w Q kh ell cnt d2 fr dd _ B' h0 hS hB fP0 fP2 fMB fbl
    hbF fhb fbl2 hT htS hR hkh s hG Bd hBd

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
