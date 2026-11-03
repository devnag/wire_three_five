import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE
import Proof.Wire_3_5.Primitive.SeedFix.C4CapG

/-! # C4 SYM stage, the stage from the setup at capacity `2^{⌊n/8⌋ + C}` (twin of `symSetup_stage`)

P3:3011-3016, 2929-2941, 2994-3000, 3034-3038, 2932-2937: `C4Cap.setup_run3`'s exit bank (capacity v2) docked on the
decision loop and the sample expansion exactly as `symSetup_stage` (same `symLay_run`):

* `symMachine3` (`setupM3 ; loop ; sample expansion`), **`symSetup_stage3`**.

Paper quantity of the main type: the stage's output `sampleWord kh (seedPairs P s)`, the fixed seed's samples. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- **The SYM stage's machine, v2**: the setup at capacity `2^{⌊n/8⌋ + Cc}`, the decision loop of `F`, the samples. -/
noncomputable def symMachine3 (L : Lay) (CL Cd Cc : ℕ) (Fp : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ)
    (C : Ledger.CapParams) (F : C4Loop.ChildFam) (pd : ℕ) (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS) :=
  wrapM (C4Cap.setupM3 L CL Cd Cc Fp cr fe ζ Cδ C) F L.oLP (hoffL L F hT) (symExt L pd) UnionMachine.SampStage.sampM
    (offF L) (hoffF L htS) (finExt L)

/-- **The SYM stage's run** from the setup's hypotheses (`C4Cap.setup_run3`), the numbers' words (`symClean`), the
numbers' links to the child family, the loop's pad and the loop's decisions. -/
theorem symSetup_stage3 (L : Lay) (hDL : 16 ≤ L.D) (CL Cd Cc : ℕ) (Fp : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ)
    (C : Ledger.CapParams) (n : ℕ) (w sfx v : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx)
    (cs : List ℕ) (cD : ℕ)
    (hd : ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ), Step Data.dataM cD (fun _ => 0)
      (Fin.addCases (Data.rawIn w n (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n))
        (fun _ : Fin 1 => List.replicate 0 false))
      (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape Data.sOUT) = Data.dataWord cs ∧ tout (sTape Data.sIN) = frame w)
    (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) (bigW Fp cr fe ζ Cδ C)
      (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)
    (hτ : ∀ j, τ.st (sk 0 (symO j)) = symClean Q kh ell cnt d2 fr dd j) (hell : 1 ≤ ell)
    (B3 : ℕ) (pre post : List Bool)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w (fr 3) (fr 2)
      (fr 4) (fr 5) pre post)
    (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT q uu : ℕ)
    (hS : ChShape F pd P ents TWd Cap nT pre post q uu)
    (e_ell : P.ell = ell) (e_kh : P.kh = kh) (e_Q : P.Q = Q) (e_ellQ : ell = max (kh + kh) (Nat.clog 2 Q))
    (e_TW : fr 0 = TWd) (e_Cap : fr 1 = Cap) (e_q : fr 2 = q) (e_dd : dd = derVals Q kh TWd Cap)
    (e_cnt : cnt = nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh)) (e_mod : P.modulus = GF.firstPrimitive ell)
    (e_uu : uu = 2 ^ d2) (e_v : v = SeedFix.blockWord ents)
    (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS) (hR : F.cellCost + 1 ≤ 2 ^ fr 6)
    (s : Fin (8 * P.ell) → Bool) (hG : SeedFix.greedyLoop F.bound F.Rv = List.ofFn s) (Bd : ℕ)
    (hBd : wrapCost (C4Cap.setupCost3 L w n CL Cd Cc cD (Data.unaryList cs) c ell d2 (fr 6) B3) F (2 ^ fr 6)
      (C4Iface.sampCost P) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run ⟨L.X, _, symMachine3 L CL Cd Cc Fp cr fe ζ Cδ C F pd hT htS⟩ Bd w v
      (FinalPass.Sample.sampleWord P.kh (C4Iface.seedPairs P s)) := by
  obtain ⟨B', st, fP0, fP1, fP2, fW, fMA, fMB, fUU, fRR, fPRE, fPOST, fLG, fmask, fbl⟩ :=
    C4Cap.setup_run3 L hDL CL Cd Cc Fp cr fe ζ Cδ C n w sfx v hw cs cD hd τ c hx hτ0
      (symClean Q kh ell cnt d2 fr dd) hτ ell (fr 3) (fr 2) (fr 4) (fr 5) d2 (fr 6) hell rfl rfl rfl rfl rfl rfl
      (by
        show [true] ++ List.replicate d2 true ++ [false] ++ List.replicate d2 false ++ [true] = _
        rw [NumsX.srcWord, NumsX.reps_single, NumsX.reps_single])
      (by
        show [true] ++ List.replicate (fr 6) true ++ [false] ++ List.replicate (fr 6) false ++ [true] = _
        rw [NumsX.srcWord, NumsX.reps_single, NumsX.reps_single])
      B3 pre post hc3
  have hB : SymBank L pd P ents TWd Cap nT pre post q uu B' (fr 6) v Q kh ell cnt d2 fr dd :=
    ⟨fW, fP1, fMA, fUU, fRR, fPRE, fPOST, fLG, fmask, e_ell, e_kh, e_Q, e_ellQ, e_TW, e_Cap, e_q, e_dd, e_cnt, e_mod,
      e_uu, e_v, hell⟩
  exact symLay_run L F pd P ents TWd Cap nT pre post q uu B' (fr 6) v w Q kh ell cnt d2 fr dd _ st hS hB fP0 fP2 fMB fbl
    hT htS hR s hG Bd hBd

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
