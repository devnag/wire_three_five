import Lean
import Proof.Wire_3_5.Primitive.Writers.HashSetH2Base
import Proof.Wire_3_5.Primitive.Writers.KWT2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.HashS1
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # HASH setup (C), P3 part 3: `setupH_run2`, the setup's run with T-c at its true cost

P3:3011-3016: `setupH_run` (M64) verbatim with T-c's contract `QCopy2` (`qCost2 q = 14q + 14`, PrimAsmKWT2) in place
of `QCopy` (whose `10q + 10` is below the copy's `14q + 4`): the same machine `M0H`, the same exit bank `HBank2`, the
setup's cost with `qCost2 (fr 2)` for the copy.

* **`setupH_run2`**.

Paper quantity of the main type: the `HBank2` at the call (the HASH stage's setup exit bank). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Run
variable (l : Literals) (F : GateFree l) (EW : Envelope) (cW K3 D3 kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
  (L : Lay) (CL Cd Cc : ℕ) (Fp : FreeProg)
  (S4 : ThrData.ThrDataStage4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
  (T : PrimThrW.PortsE.TopFrontPort3 ((gate0 l F).alg)) (N : PrimThrW.Nums4.NumsPort4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D) (Wk : PrimT.C4KW.KWW) (fT : ℕ)

/-- **The HASH setup's run at a THR call** to the `HBank2`, v2: T-c at `QCopy2` (its true cost `qCost2`). -/
theorem setupH_run2 (C3 : C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0) (hL : L.S3 = C3.thr)
    (hDL : 16 ≤ L.D)
    (hDR : PrimT.C4KW.DataRerun S4 (XH L S4 T N Wk fT) (oD L S4) (hDD L S4 T N Wk fT) (g0 L S4 T N Wk fT) (tNt L S4 T N Wk fT) (tLt L S4 T N Wk fT) (tDt L S4 T N Wk fT))
    (hKW : PrimT.C4KW.KwDock Wk (XH L S4 T N Wk fT) (oK L S4 T N) (hKK L S4 T N Wk fT) (kInH L S4 T N Wk fT))
    (hQC : PrimT.C4KW.QCopy2 (XH L S4 T N Wk fT) (oQ L S4 T N Wk) (hQQ L S4 T N Wk fT) (srcQ L S4 T N Wk fT))
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation)) (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value L.D CL n)
    (hLW : UnaryCalc.value L.D CL n ≤ (UnaryCalc.value L.D Cd n))
    (hcu : 2 * (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs)).length + 2 * UnaryCalc.value L.D CL n ≤ 2 * (UnaryCalc.value L.D Cd n))
    (hneed : S4.need n ≤ 2 * (UnaryCalc.value L.D Cd n) + 2)
    (hfit : ThrCap.ThrFitAt Fp F.cr F.filterErrDeg (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) ha Cs carriers translation hs)
    (hfx : ThrCap.HashFitX Fp (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs) (dg : ℕ)
    (h1 : 1 ≤ (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3)
    (hcf : CompilerMachine.Pool.CoefFit ((gate0 l F).alg) (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs) (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
      (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0))
    (hload : (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3 + (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2 + (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 4 + (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 5 ≤ K3 * ((((gate0 l F).budget kclk coef A a0 ha0).psiOf n) + 1) * (n + 1) ^ D3)
    (hrP : ((callInputs l F kclk coef A a0 ha0).starParams n hs).r = Ledger.rowBr F.cr n) (hn1 : 1 ≤ n) (hcapT : 1 ≤ ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap)
    (hok : PrimThrW.TopFront2.TF2Ok Cs (carriers.map Carrier.code) (UnaryCalc.value L.D Cd n))
    (hnd : N.need (n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ≤ (UnaryCalc.value L.D Cd n)) (Bm Sm : ℕ)
    (hcf2 : HashCell.CellFit ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation F.cr Bm Sm (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2)) :
    ∃ (c0 : ℕ) (B : Fin (3 + (XH L S4 T N Wk fT)) → List Bool),
      Step (M0H L S4 T N Wk fT CL Cd Cc F.cr (ThrNums.bigWTH Fp F.cr F.filterErrDeg)) c0 (fun _ => 0)
        (PrimT.SeedFixTypes.stageIn (XH L S4 T N Wk fT) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) (fun _ => 0) B ∧
      PrimT.C4H.HBank2 L (hLxH L S4 T N Wk fT) B (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (C4Child.pre ((gate0 l F).alg) (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0 ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 4) dg ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 5) 0)) (C4Child.post ((gate0 l F).alg) (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0 ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 4) dg ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 5) 0))
        (PrimT.C4H.hb0 (PrimT.C4H.hbX (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (FinalPass.HashFr.capsOf ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1)) 0 0)) (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0 ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 4) dg ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 5) 0).P.Q
        (2 ^ PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) * 2 ^ PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 6) (hkTH L S4 T N Wk fT) (hqTH L S4 T N Wk fT) (hOff L S4 T N Wk) ∧
      c0 ≤ ThrSet.setupT3Cost L (thrReq n a ha Cs carriers translation).word n CL Cd Cc (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) (2 ^ PrimT.C4Cap.capExp2 Cc n)
          (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n)
            translation.length ([] : List Bool).length (RepairRepresentation.natListWord translation).length)
          (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs) ++ ThrData.thrCounts Cs carriers))
          (ThrNums.hashBigCost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length
            (PrimT.C4GateSym.needW n) ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs).getD 12 0) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)))
          (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs Cs)))
          (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 6)
          (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
            (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))
        + 1 + (C4Cap.frontCost3 L (thrReq n a ha Cs carriers translation).word n CL Cd Cc + 1 + (C4Cap.frontCost3 L (thrReq n a ha Cs carriers translation).word n CL Cd Cc + 1 +
          (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n) + 1 +
            C4Set.cpZCost (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ++ ThrData.thrCounts Cs carriers)) + 1 +
            (HashCell.callCost ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation T N F.cr (UnaryCalc.value L.D Cd n) (2 ^ PrimT.C4Cap.capExp2 Cc n) Bm Sm + 1 +
              (Wk.cost (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1) + 1 + PrimT.C4KW.qCost2 ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2)))))) := by
  obtain ⟨hk2, hdesc, he⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hxb : xb L S4 = ThrSet.thrXb L S4.x3 := rfl
  have hNX : L.N = 3 + L.X := rfl
  -- 1: the THR setup chain (M58), lifted onto the bank
  obtain ⟨c, B', hc, hB, fP0, fP1, fP2, fW, fUU, fRR, fPRE, fPOST, fLG, fmask, fbl, fbl2⟩ :=
    HashSet.hash_setup_run l F EW cW K3 D3 kclk coef A a0 ha0 C3 L hL hDL CL Cd Cc Fp S4 ha Cs carriers translation hcall
      hs hWL hLW hcu hneed hfit hfx dg h1 hcf hload
  have hinjL := BigBank.liftE_inj (hxX L S4 T N Wk fT)
  have s1 := hB.focus (BigBank.liftE (hxX L S4 T N Wk fT)) hinjL (fun _ => 0) (PrimT.SeedFixTypes.stageIn (XH L S4 T N Wk fT) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers))
  have hdz : dockH (BigBank.liftE (hxX L S4 T N Wk fT)) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, BigBank.liftE (hxX L S4 T N Wk fT) j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [dockH_slot _ hinjL]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  have hins : install (BigBank.liftE (hxX L S4 T N Wk fT)) (PrimT.SeedFixTypes.stageIn (XH L S4 T N Wk fT) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers))
      (PrimT.SeedFixTypes.stageIn (ThrSet.thrXb L S4.x3) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) = PrimT.SeedFixTypes.stageIn (XH L S4 T N Wk fT) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) :=
    install_existing _ _ _ (fun j => by rw [stageIn_val, stageIn_val, BigBank.liftE_val])
  rw [hdz, hins] at s1
  set B1 := install (BigBank.liftE (hxX L S4 T N Wk fT)) (PrimT.SeedFixTypes.stageIn (XH L S4 T N Wk fT) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) B' with hB1
  have b1lo : ∀ (i : Fin (3 + (XH L S4 T N Wk fT))) (hi : i.val < 3 + ThrSet.thrXb L S4.x3), B1 i = B' ⟨i.val, hi⟩ := fun i hi => by
    have := install_slot (BigBank.liftE (hxX L S4 T N Wk fT)) hinjL (PrimT.SeedFixTypes.stageIn (XH L S4 T N Wk fT) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) B' ⟨i.val, hi⟩
    exact this
  have b1L : ∀ k : Fin L.N, B1 ⟨k.val, by have := k.isLt; have := hLxH L S4 T N Wk fT; omega⟩ =
      B' (BigBank.liftE (ThrSet.hxb L S4.x3) k) := fun k => by
    rw [b1lo _ (by show (k : ℕ) < 3 + ThrSet.thrXb L S4.x3; have := k.isLt; have := LN_le L S4; omega)]
    rfl
  have b1hi : ∀ i : Fin (3 + (XH L S4 T N Wk fT)), oF1 L S4 ≤ i.val → B1 i = [] := fun i hi => by
    have hoF1' : oF1 L S4 = 3 + ThrSet.thrXb L S4.x3 := rfl
    rw [hB1, install_other _ _ _ _ (fun j h => by
      have := congrArg Fin.val h; rw [BigBank.liftE_val] at this; have := j.isLt; omega), stageIn_val]
    rw [if_neg (by omega), if_neg (by omega)]
  have hB10 : B1 (g0 L S4 T N Wk fT) = frame (thrReq n a ha Cs carriers translation).word := by
    have := b1L L.gP0
    rw [fP0] at this
    exact this
  -- 2, 3: the two front copies
  obtain ⟨sfx, hw⟩ : ∃ sfx, (thrReq n a ha Cs carriers translation).word = RepairRepresentation.natWord n ++ sfx :=
    ⟨_, by unfold PrimRequest.word; simp only [List.append_assoc]; rfl⟩
  have hoF1'' : oF1 L S4 = 3 + ThrSet.thrXb L S4.x3 := rfl
  have hoF2'' : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD'' : oD L S4 = oF2 L S4 + L.N := rfl
  have hg1 : (g0 L S4 T N Wk fT).val < oF1 L S4 := by rw [val_g0]; omega
  obtain ⟨B2, s2, e20, e2N, e2L, e2D, e2W, e2u, e2bl⟩ := HashSet.front_copy L hDL CL Cd Cc n (thrReq n a ha Cs carriers translation).word sfx hw (oF1 L S4)
    (hF1 L S4 T N Wk fT) (g0 L S4 T N Wk fT) hg1 B1 hB10 b1hi
  obtain ⟨B3, s3, e30, e3N, e3L, e3D, e3W, e3u, e3bl⟩ := HashSet.front_copy L hDL CL Cd Cc n (thrReq n a ha Cs carriers translation).word sfx hw (oF2 L S4)
    (hF2 L S4 T N Wk fT) (g0 L S4 T N Wk fT) (by rw [val_g0]; omega) B2 e20
    (fun i hi => e2bl i (by omega))
  -- 4: T-a (the data stage's rerun and copy-in)
  obtain ⟨hL', hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu', -, -⟩ := PrimT.C4GateSym.thr_data_hyps Cs carriers ha hk2 hdesc he
    (UnaryCalc.value L.D CL n) hWL
  have hua : (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs) ++ ThrData.thrCounts Cs carriers)).length =
      (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs)).length + (Data.unaryList (ThrData.thrCounts Cs carriers)).length := by
    unfold Data.unaryList
    rw [List.flatMap_append, List.length_append]
  have hcu2 : 2 * (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs) ++ ThrData.thrCounts Cs carriers)).length + 2 ≤
      2 * (UnaryCalc.value L.D Cd n) + 2 := by omega
  have hcN2 : natBitLength n + 1 ≤ 2 * (UnaryCalc.value L.D Cd n) + 2 := by omega
  have hcA2 : 2 ^ (natBitLength a + 1) ≤ 2 * (UnaryCalc.value L.D Cd n) + 2 := by omega
  have hcK2 : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * (UnaryCalc.value L.D Cd n) + 2 := by omega
  have hcx2 : ∀ x ∈ ReqBridge.thrCodes Cs,
      2 * (RepairRepresentation.natWord x).length + 2 + n + UnaryCalc.value L.D CL n ≤ 2 * (UnaryCalc.value L.D Cd n) + 2 :=
    fun x hx => by have := hcx x hx; omega
  have hcy2 : ∀ y ∈ carriers.map Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + UnaryCalc.value L.D CL n ≤ 2 * (UnaryCalc.value L.D Cd n) + 2 :=
    fun y hy => by have := hcy y hy; omega
  obtain ⟨tout, m, J, h3, hO, hI⟩ := ThrSet.thr_hd S4 ((callInputs l F kclk coef A a0 ha0).starParams n hs) ha Cs carriers translation [] (UnaryCalc.value L.D CL n)
    (UnaryCalc.value L.D Cd n) hk2 hL' hLX h2 hcN2 hcA2 hcK2 hcx2 hcy2 hcu2 hdesc hneed
  rw [List.append_nil] at h3 hI
  have hout := L.out_lt
  have hU := L.U_pos
  have hNq := L.N_eq
  have hlo : ∀ (i : Fin (3 + (XH L S4 T N Wk fT))), i.val < oF2 L S4 → i ≠ g0 L S4 T N Wk fT → B3 i = B2 i := fun i h h' => e3u i h h'
  have tN_ne : tNt L S4 T N Wk fT ≠ g0 L S4 T N Wk fT := fun e => by have := congrArg Fin.val e; rw [val_tN, val_g0] at this; omega
  have tL_ne : tLt L S4 T N Wk fT ≠ g0 L S4 T N Wk fT := fun e => by have := congrArg Fin.val e; rw [val_tL, val_g0] at this; omega
  have tD_ne : tDt L S4 T N Wk fT ≠ g0 L S4 T N Wk fT := fun e => by have := congrArg Fin.val e; rw [val_tD, val_g0] at this; omega
  obtain ⟨B4, s4, e4U, e40, e4u⟩ := hDR
    (fun e => by have := congrArg Fin.val e; rw [val_g0, val_tN] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [val_g0, val_tL] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [val_g0, val_tD] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [val_tN, val_tL] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [val_tN, val_tD] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [val_tL, val_tD] at this; omega)
    (by rw [val_g0]; omega) (by rw [val_tN]; omega) (by rw [val_tL]; omega) (by rw [val_tD]; omega)
    (thrReq n a ha Cs carriers translation).word n (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n) (ThrData.hashNums ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ++ ThrData.thrCounts Cs carriers) (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) tout m J B3
    h3 hO hI e30
    (by rw [hlo _ (by rw [val_tN]; omega) tN_ne]; exact e2N)
    (by rw [hlo _ (by rw [val_tL]; omega) tL_ne]; exact e2L)
    (by rw [hlo _ (by rw [val_tD]; omega) tD_ne]; exact e2D)
    (fun i h1 h2 => e3bl i (by omega))
  -- 5: the HASH cell
  obtain ⟨τF, mc, sC, f0, f113, f2, fK⟩ := HashCell.cell_call ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation T N F.cr (UnaryCalc.value L.D Cd n)
    (2 ^ PrimT.C4Cap.capExp2 Cc n) Bm Sm hrP hn1 hdesc hk2 hcapT hok hnd hcf2
  have hinjE := extC_inj L S4 T N Wk fT
  have hltE := extC_lt L S4 T N Wk fT
  have d10 : HashCell.bIn (cX T N) (sTape (nr := LNR) (sk (cX T N) 113)) ≠ HashCell.bIn (cX T N) (sTape (sk (cX T N) 0)) :=
    fun e => sTne _ 113 0 (by decide) (bIn_inj _ e)
  have d20 : HashCell.bIn (cX T N) (sTape (nr := LNR) (sk (cX T N) 2)) ≠ HashCell.bIn (cX T N) (sTape (sk (cX T N) 0)) :=
    fun e => sTne _ 2 0 (by decide) (bIn_inj _ e)
  have d21 : HashCell.bIn (cX T N) (sTape (nr := LNR) (sk (cX T N) 2)) ≠
      HashCell.bIn (cX T N) (sTape (sk (cX T N) 113)) :=
    fun e => sTne _ 2 113 (by decide) (bIn_inj _ e)
  obtain ⟨kv, kw⟩ := keep_vw L S4 T N Wk fT B3 B4 e4u
  have hexE : ∀ j g, extC L S4 T N Wk fT j = some g → B4 g = Fin.addCases (rawX (cX T N) (thrReq n a ha Cs carriers translation).word
      (HashCell.cu ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (UnaryCalc.value L.D Cd n) (2 ^ PrimT.C4Cap.capExp2 Cc n)) (fun _ : Fin 1 => []) j := by
    intro j g hj
    rcases extC_cases L S4 T N Wk fT j g hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Fin.addCases_left, e40]
      simp only [rawX, if_true]
    · rw [Fin.addCases_left]
      simp only [rawX, if_neg d10, if_true]
      exact e4U
    · rw [Fin.addCases_left, kv]
      simp only [rawX, if_neg d20, if_neg d21, if_true]
      exact e3D
    · rw [Fin.addCases_left, kw]
      simp only [rawX, (HashCell.bIn_ne_cnt _ _).symm, if_false, if_true]
      exact e3W
  have hblE := up_blank L S4 T N Wk fT B3 B4 e4u e3bl
  have htinE : ∀ j, extC L S4 T N Wk fT j = none → Fin.addCases (m := BX (cX T N)) (n := 1) (motive := fun _ => List Bool)
      (rawX (cX T N) (thrReq n a ha Cs carriers translation).word (HashCell.cu ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (UnaryCalc.value L.D Cd n) (2 ^ PrimT.C4Cap.capExp2 Cc n)) (fun _ : Fin 1 => []) j = [] := by
    intro j hj
    by_cases hjl : j.val < BX (cX T N)
    · have ej : j = Fin.castAdd 1 ⟨j.val, hjl⟩ := Fin.ext rfl
      rw [ej] at hj ⊢
      rw [Fin.addCases_left]
      have n0 : (⟨j.val, hjl⟩ : Fin (BX (cX T N))) ≠ HashCell.bIn (cX T N) (sTape (sk (cX T N) 0)) := fun e => by
        rw [e] at hj; simp [extC] at hj
      have n1 : (⟨j.val, hjl⟩ : Fin (BX (cX T N))) ≠ HashCell.bIn (cX T N) (sTape (sk (cX T N) 113)) := fun e => by
        rw [e] at hj; simp [extC, c_ne T N 113 0 (by decide)] at hj
      have n2 : (⟨j.val, hjl⟩ : Fin (BX (cX T N))) ≠ HashCell.bIn (cX T N) (sTape (sk (cX T N) 2)) := fun e => by
        rw [e] at hj; simp [extC, c_ne T N 2 0 (by decide), c_ne T N 2 113 (by decide)] at hj
      have n3 : (⟨j.val, hjl⟩ : Fin (BX (cX T N))) ≠ bCnt (cX T N) := fun e => by
        rw [e] at hj
        simp [extC, (c_ne_cnt T N 0).symm, (c_ne_cnt T N 113).symm, (c_ne_cnt T N 2).symm] at hj
      simp only [rawX, if_neg n0, if_neg n1, if_neg n2, if_neg n3]
    · rw [show j = Fin.natAdd (BX (cX T N)) (0 : Fin 1) from Fin.ext (by simp; omega), Fin.addCases_right]
  obtain ⟨s5, bl5, un5, sl5, ex5⟩ := C4Set.stageP sC (oC L S4) (hCC L S4 T N Wk fT) (extC L S4 T N Wk fT) hinjE hltE B4 hexE hblE
    htinE
  obtain ⟨B5, hB5⟩ : ∃ B5, B5 = install (slx (oC L S4) (hCC L S4 T N Wk fT) (extC L S4 T N Wk fT)) B4 (Fin.addCases (Fin.addCases
    (wenc (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) τF).A (HashCell.xB (2 ^ PrimT.C4Cap.capExp2 Cc n))) (fun _ : Fin 1 => List.replicate mc false)) := ⟨_, rfl⟩
  rw [← hB5] at s5 bl5 un5 sl5 ex5
  have hg5 : B5 (g0 L S4 T N Wk fT) = B1 (g0 L S4 T N Wk fT) := by
    rw [hB10, ex5 (Fin.castAdd 1 (HashCell.bIn (cX T N) (sTape (sk (cX T N) 0)))) (g0 L S4 T N Wk fT) (by simp [extC]),
      Fin.addCases_left, HashCell.bIn, Fin.addCases_left, wenc_A_s]
    exact f0
  have low5 := low_chain L S4 T N Wk fT B1 B2 B3 B4 B5 e2u e3u e4u un5 hg5
  obtain ⟨sm1, sm2, sm3, sm4, sm5, sm6⟩ := small_lt L S4 T N Wk fT
  -- 6: T-b
  have hin6 : ∀ i : Fin 12, B5 (kInH L S4 T N Wk fT i) = PrimT.C4KW.kwIns (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1) i := by
    intro i
    by_cases i0 : i.val = 0
    · have e : kInH L S4 T N Wk fT i = ⟨L.gP1.val, lt_of_lt_of_le L.gP1.isLt (hLxH L S4 T N Wk fT)⟩ :=
        Fin.ext (by rw [kInH_val, if_pos i0]; rfl)
      rw [e, low5 _ sm1, b1L L.gP1, fP1, show i = 0 from Fin.ext i0, hashTape_htWord ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs Cs carriers]
      rfl
    · by_cases i10 : i.val = 10
      · have e : kInH L S4 T N Wk fT i = ⟨(L.gW 3).val, lt_of_lt_of_le (L.gW 3).isLt (hLxH L S4 T N Wk fT)⟩ :=
          Fin.ext (by rw [kInH_val, if_neg i0, if_pos i10])
        rw [e, low5 _ (sm2 3), b1L (L.gW 3), fW 3, show i = 10 from Fin.ext i10]
        rfl
      · have hk := kS_ge i i0 i10
        have hk2' := (kS i).isLt
        have ext0 : extC L S4 T N Wk fT (Fin.castAdd 1 (HashCell.bIn (cX T N) (sTape (sk (cX T N) (kS i))))) = none := by
          simp [extC, c_ne T N (kS i) 0 (by omega), c_ne T N (kS i) 113 (by omega), c_ne T N (kS i) 2 (by omega),
            c_ne_cnt T N (kS i)]
        have hv : (kInH L S4 T N Wk fT i).val = oC L S4 + (Fin.castAdd 1 (HashCell.bIn (cX T N) (sTape (nr := LNR)
            (sk (cX T N) (kS i))))).val := by
          rw [kInH_val, if_neg i0, if_neg i10]
          simp only [Fin.val_castAdd, HashCell.bIn_val, DockW.sTape_val, sk_val]
          rw [if_neg (by omega)]
          omega
        rw [sl5 _ _ ext0 hv, Fin.addCases_left, HashCell.bIn, Fin.addCases_left, wenc_A_s]
        exact fK ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1) i i0 i10
  obtain ⟨B6, s6, e6K, e6u, -⟩ := hKW (kInH_inj L S4 T N Wk fT) (fun i => kInH_lt L S4 T N Wk fT i) (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1) B5 hin6
    (fun i h1 h2 => bl5 i h1)
  -- 7: T-c
  have hsrc : B6 (srcQ L S4 T N Wk fT) = List.replicate ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) true := by
    rw [e6u _ (Or.inl (lt_of_lt_of_le sm3 sm4)), low5 _ sm3]
    rw [show srcQ L S4 T N Wk fT = ⟨(L.gW 34).val, lt_of_lt_of_le (L.gW 34).isLt (hLxH L S4 T N Wk fT)⟩ from rfl, b1L (L.gW 34), fW 34]
    rfl
  obtain ⟨B7, s7, e7Q, e7u, -⟩ := hQC (lt_of_lt_of_le sm3 sm5) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) B6 hsrc
    (fun i h1 h2 => by
      rw [e6u i (Or.inr h1)]
      exact bl5 i (le_trans (le_trans (Nat.le_add_right (oK L S4 T N) 94) (Nat.le_add_right _ Wk.x)) h1))
  -- the exit bank
  obtain ⟨tc1, tc2, tc3, -, -⟩ := tail_chain L S4 T N Wk fT B5 B6 B7 e6u e7u bl5
  have low7 : ∀ i : Fin (3 + (XH L S4 T N Wk fT)), i.val < oF1 L S4 → B7 i = B1 i := fun i hi => by
    rw [tc1 i (lt_of_lt_of_le hi sm6), low5 i hi]
  have lowL : ∀ k : Fin L.N, B7 ⟨k.val, lt_of_lt_of_le k.isLt (hLxH L S4 T N Wk fT)⟩ =
      B' (BigBank.liftE (ThrSet.hxb L S4.x3) k) := fun k => by
    rw [low7 _ (lt_of_lt_of_le k.isLt (LN_le L S4))]
    exact b1L k
  obtain ⟨ba1, ⟨ba2, ba3, ba4⟩, ba5⟩ := bank_arith L S4 T N Wk fT
  refine ⟨_, B7, Step.seq s1 (Step.seq s2 (Step.seq s3 (Step.seq s4 (Step.seq s5 (Step.seq s6 s7))))),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, e7Q, ba5, ba1, ⟨ba2, ba3, ba4⟩, tc2⟩, ?_⟩
  · exact (lowL L.gP0).trans fP0
  · exact (lowL L.gP1).trans fP1
  · exact (lowL L.gP2).trans fP2
  · rw [show (2 : ℕ) ^ PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) * 2 ^ PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) =
        2 ^ (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) by rw [Nat.zero_add, pow_add]]
    exact (lowL L.gUU).trans fUU
  · exact (lowL L.gRR).trans fRR
  · exact (lowL L.gPRE).trans fPRE
  · exact (lowL L.gPOST).trans fPOST
  · exact (lowL L.gLG).trans fLG
  · intro i hi
    exact (lowL i).trans (fmask i hi)
  · intro i hi
    exact (lowL i).trans (fbl i hi)
  · intro j
    exact (tc3 j).trans (e6K j)
  · exact Nat.add_le_add_right (Nat.add_le_add_right (cost_mono L _ n CL Cd Cc _ _ _ _ c _ _ _ _ _ hc) 1) _

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.HashSetH

end
