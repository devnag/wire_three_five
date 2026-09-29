import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf4
import Proof.Wire_3_5.Primitive.Writers.HashSetH3

/-! # The HASH part of C4Leaf, v3: T-c at its true cost (`QCopy2`, `qCost2 q = 14q + 14`)

The HashLf/HashLf3 (M77/M78) with the setup's copy `1^{Q'}` charged `qCost2` (`QCopy` at `10q + 10` is below the
copy's `14q + 4`): the setup's cost **`hashC0Q`** (`hashC0` with `qCost2`), **`HashStepsAt3`** (`HashStepsAt2` at
`hashC0Q`), `hash_at_call3` (`setupH_run2`, then `hash_call_run`), **`HashObl3`** (`HashSideAt2` unchanged,
`HashStepsAt3`), `hashLeafC4_of3`, `hashLeafC4_3`, **`c4Leaf_of_obl3 : … → ∀ l, C4Leaf l`** (T-c's hypothesis
`QCopy2`). Same shapes otherwise; M77/M78 untouched.

Paper quantity of the main type: the HASH stage's run at a THR call within the seed-fixing budget (P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashCell NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- (v3, `qCost2`) The HASH setup's explicit cost at a THR call (`setupH_run`'s bound). -/
noncomputable def hashC0Q (l : Literals) (F : GateFree l) (EW : Envelope) (cW K3 D3 kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (L : Lay) (CL Cd Cc : ℕ) (Fp : FreeProg)
    (S4 : ThrData.ThrDataStage4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
    (T : PrimThrW.PortsE.TopFrontPort3 ((gate0 l F).alg)) (N : PrimThrW.Nums4.NumsPort4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D) (Wk : PrimT.C4KW.KWW) (fT : ℕ)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (Bm Sm : ℕ) : ℕ :=
  ThrSet.setupT3Cost L (thrReq n a ha Cs carriers translation).word n CL Cd Cc (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) (2 ^ PrimT.C4Cap.capExp2 Cc n)
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
              (Wk.cost (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1) + 1 + PrimT.C4KW.qCost2 ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2))))))

/-- **(C): the HASH stage's steps within the seed budget** at every THR call of the family (`hash_steps_gen`,
the twin of `thr_steps_gen`): the setup's cost `hashC0Q`, the pre-loop stage, the pad, the loop over the HASH child
family `hashFamCall`, the finisher. -/
def HashStepsAt3 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
    (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (EW : Envelope) (cW kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (L : Lay) (CL Cd Cc : ℕ)
    (S4 : ThrData.ThrDataStage4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
    (T : PrimThrW.PortsE.TopFrontPort3 ((gate0 l F).alg)) (N : PrimThrW.Nums4.NumsPort4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D) (Wk : PrimT.C4KW.KWW) (fT : ℕ) (E4 : Envelope) (c₄ : ℕ) : Prop :=
  ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (Bm Sm : ℕ),
    HashCell.CellFit ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation F.cr Bm Sm (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) → Bm ≤ 2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2 →
    wrapCost (hashC0Q l F EW cW K3 D3 kclk coef A a0 ha0 L CL Cd Cc H.Fp S4 T N Wk fT ha Cs carriers translation hs Bm Sm + 1 + (2 * preCost (thrReq n a ha Cs carriers translation).word (2 * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t) (2 * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) + 2 + 1 + (2 * 2 ^ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 6 + 4))) (C4Hf.hashFamCall (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation UnionMachine.TailAsm.asmStage wa (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 5) 0) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0 rfl rfl rfl (FinalPass.HashFr.capsOf ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1)) E4 (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) (H.Kc n) (H.Kch n) (H.caps_ge kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs) (H.side kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs)).F
      (2 ^ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 6) (finCost (thrReq n a ha Cs carriers translation).word (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a0 ha0).starParams n hs) (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a0 ha0).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)))) + 1 ≤
      c₄ * seedClasses E4 n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n)

section Call
variable (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
  (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (EW : Envelope) (cW kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
  (L : Lay) (CL Cd Cc : ℕ)
  (S4 : ThrData.ThrDataStage4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
  (T : PrimThrW.PortsE.TopFrontPort3 ((gate0 l F).alg)) (N : PrimThrW.Nums4.NumsPort4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D) (Wk : PrimT.C4KW.KWW)

/-- **The HASH stage at a THR call** within `c₄·seedClasses E₄`: the setup run, then the stage run. -/
theorem hash_at_call3 (E4 : Envelope) (c₄ : ℕ) (C3 : C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0)
    (hL : L.S3 = C3.thr) (hDL : 16 ≤ L.D)
    (hDR : PrimT.C4KW.DataRerun S4 (XH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (oD L S4)
      (hDD L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (g0 L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T)
      (tNt L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (tLt L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T)
      (tDt L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T))
    (hKW : PrimT.C4KW.KwDock Wk (XH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (oK L S4 T N)
      (hKK L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (kInH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T))
    (hQC : PrimT.C4KW.QCopy2 (XH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (oQ L S4 T N Wk)
      (hQQ L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (srcQ L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T))
    (hside : HashSideAt2 l F wa K3 D3 Kp Dp H EW cW kclk coef A a0 ha0 L CL Cd Cc S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T)
    (hsteps : HashStepsAt3 l F wa K3 D3 Kp Dp H EW cW kclk coef A a0 ha0 L CL Cd Cc S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T E4 c₄)
    (hc1 : 1 ≤ F.CD) {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value L.D CL n)
    (hLW : UnaryCalc.value L.D CL n ≤ (UnaryCalc.value L.D Cd n))
    (hcu : 2 * (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs)).length + 2 * UnaryCalc.value L.D CL n ≤ 2 * (UnaryCalc.value L.D Cd n))
    (hneed : S4.need n ≤ 2 * (UnaryCalc.value L.D Cd n) + 2) :
    SeedFixTypes.Stage3Run (hashStageH (l := l) (F := F) (wa := wa) (K3 := K3) (D3 := D3) (Kp := Kp) (Dp := Dp) (H := H) (kclk := kclk) (coef := coef) (A := A) (a0 := a0) (ha0 := ha0) (L := L) (CL := CL) (Cd := Cd) (Cc := Cc) (S4 := S4) (T := T) (N := N) (Wk := Wk))
      (c₄ * seedClasses E4 n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))
      (thrReq n a ha Cs carriers translation).word (hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
      (frame (SeedFixTypes.thrIn l F kclk coef A a0 ha0 n a ha Cs carriers translation hs)) := by
  obtain ⟨hfit, hfx, h1, hcf, hrP, hn1, hcapT, hok, hnd, Bm, Sm, hcf2, hBm⟩ := hside ha Cs carriers translation hcall hs
  obtain ⟨c0, B, h0, hB, hc0⟩ := setupH_run2 l F EW cW K3 D3 kclk coef A a0 ha0 L CL Cd Cc H.Fp S4 T N Wk
    (famUH UnionMachine.TailAsm.asmStage wa).T C3 hL hDL hDR hKW hQC ha Cs carriers translation hcall hs hWL hLW hcu hneed
    hfit hfx (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) h1 hcf
    (H.c3_le hc1 kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs) hrP hn1 hcapT hok hnd Bm Sm hcf2
  have hst := hsteps ha Cs carriers translation hcall hs Bm Sm hcf2 hBm
  have hc0' : c0 ≤ hashC0Q l F EW cW K3 D3 kclk coef A a0 ha0 L CL Cd Cc H.Fp S4 T N Wk
      (famUH UnionMachine.TailAsm.asmStage wa).T ha Cs carriers translation hs Bm Sm := hc0
  refine hash_call_run l F wa K3 D3 Kp Dp H kclk coef A a0 ha0 L _ _ _ _ _ _ n a ha Cs carriers translation hcall hs E4 B
    h0 hB _ ?_
  unfold wrapCost at hst ⊢
  omega

end Call

/-- **The deliverable at an admissible `F`** (the capacity constant `C_c`, the stage constant `c₄`, the side
conditions and (C) at every call family, the C3 writer `W`). -/
def HashObl3 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
    (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (EW : Envelope) (cW : ℕ)
    (W : ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1), C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0)
    (Cnw Dnw : ℕ) (Wk : PrimT.C4KW.KWW) (E4 : Envelope) : Type :=
  Σ' Cc c₄ : ℕ, (∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1),
      HashSideAt2 l F wa K3 D3 Kp Dp H EW cW kclk coef A a0 ha0 (PrimT.C4SymLf.symLay wa (W kclk coef A a0 ha0).thr (hDl l Dnw))
        (Cnw + 1) (hCd l F Cnw) Cc (PrimT.TS4.stage4At l F kclk coef A a0 ha0) (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg)
        (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D) Wk (famUH UnionMachine.TailAsm.asmStage wa).T) ∧
    (∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1),
      HashStepsAt3 l F wa K3 D3 Kp Dp H EW cW kclk coef A a0 ha0 (PrimT.C4SymLf.symLay wa (W kclk coef A a0 ha0).thr (hDl l Dnw))
        (Cnw + 1) (hCd l F Cnw) Cc (PrimT.TS4.stage4At l F kclk coef A a0 ha0) (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg)
        (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D) Wk (famUH UnionMachine.TailAsm.asmStage wa).T E4 c₄)

/-- **The HASH part of C4Leaf** from the HASH builder, PA's C3 request writers, the v4 data stage, the kept words
writer and stage contracts, and the per-`F` obligations. -/
noncomputable def hashLeafC4_of3 (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) (Cnw Dnw : ℕ)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) (W3 : C3ReqIface3.C3ReqLeaf3 l) (Wk : PrimT.C4KW.KWW)
    (hDR : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.DataRerun S4 (XH L S4 T N Wk fT) (oD L S4) (hDD L S4 T N Wk fT) (g0 L S4 T N Wk fT)
        (tNt L S4 T N Wk fT) (tLt L S4 T N Wk fT) (tDt L S4 T N Wk fT))
    (hKW : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.KwDock Wk (XH L S4 T N Wk fT) (oK L S4 T N) (hKK L S4 T N Wk fT) (kInH L S4 T N Wk fT))
    (hQC : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.QCopy2 (XH L S4 T N Wk fT) (oQ L S4 T N Wk) (hQQ L S4 T N Wk fT) (srcQ L S4 T N Wk fT))
    (hobl : ∀ (fe CDs K3 D3 Kp Dp : ℕ) (F : GateFree l) (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp)
      (EW : Envelope) (cW : ℕ) (W : ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1), C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0),
      F.filterErrDeg = fe → ClassLE (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) F.E →
      HashObl3 l F wa K3 D3 Kp Dp H EW cW W Cnw Dnw Wk (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp))) :
    PrimT.C4K.HashLeafC4 l := by
  intro fe
  obtain ⟨CDs, K3, D3, Kp, Dp, mk⟩ := FinalPass.HashFr.hashFreeOk2 l wa fe
  obtain ⟨EW, CDW, mkW⟩ := W3 K3 D3 fe
  refine ⟨PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp), max (max CDs CDW) 1, fun F hfe hE hCD => ?_⟩
  have hEW : ClassLE EW F.E := PrimT.C4K.classLE_trans (PrimT.C4K.le_emax_left EW _) hE
  have hcp : 1 ≤ F.E.cpsi := (PrimT.C4K.le_emax_right EW (PrimT.C4SymLf.symFloor Dp)).cpsi.trans hE.cpsi
  have hCDs : CDs ≤ F.CD := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD
  have hCDW : CDW ≤ F.CD := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD
  have hCD1 : 1 ≤ F.CD := le_trans (le_max_right _ _) hCD
  have H := mk F hfe hCDs hcp
  obtain ⟨cW, W⟩ := mkW F hfe hEW hCDW
  obtain ⟨Cc, c₄, hside, hsteps⟩ := hobl fe CDs K3 D3 Kp Dp F H EW cW W hfe hE
  refine ⟨c₄, fun kclk coef A a ha =>
    ⟨hashStageH (l := l) (F := F) (wa := wa) (K3 := K3) (D3 := D3) (Kp := Kp) (Dp := Dp) (H := H) (kclk := kclk)
      (coef := coef) (A := A) (a0 := a) (ha0 := ha) (L := PrimT.C4SymLf.symLay wa (W kclk coef A a ha).thr (hDl l Dnw))
      (CL := Cnw + 1) (Cd := hCd l F Cnw) (Cc := Cc) (S4 := PrimT.TS4.stage4At l F kclk coef A a ha)
      (T := PrimThrW.TF3Cost.topFront3 (gate0 l F).alg) (N := PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a ha).D) (Wk := Wk),
      fun n a' ha' Cs carriers translation hcall hs => ?_⟩⟩
  obtain ⟨hWL, hLW, hcu, hneed⟩ := ThrLf.thr_data_W l F kclk coef A a ha ha' Cs carriers translation hcall hs Cnw Dnw (hnw n)
    (PrimT.TS4.NCoef l F.cr) (PrimT.TS4.NDeg l) ((PrimT.TS4.stage4At l F kclk coef A a ha).need n)
    ((PrimT.TS4.stage4At l F kclk coef A a ha).need_le n)
  exact hash_at_call3 l F wa K3 D3 Kp Dp H EW cW kclk coef A a ha (PrimT.C4SymLf.symLay wa (W kclk coef A a ha).thr (hDl l Dnw))
    (Cnw + 1) (hCd l F Cnw) Cc (PrimT.TS4.stage4At l F kclk coef A a ha) (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg)
    (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a ha).D) Wk (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) c₄
    (W kclk coef A a ha) rfl (by show 16 ≤ hDl l Dnw + 16; omega) (hDR _ _ _ _ _) (hKW _ _ _ _ _) (hQC _ _ _ _ _)
    (hside kclk coef A a ha) (hsteps kclk coef A a ha) hCD1 ha' Cs carriers translation hcall hs hWL hLW hcu hneed

/-- **The HASH part of C4Leaf** at the gate's Williams algorithm `waOf l` and `needW`'s polynomial bound. -/
noncomputable def hashLeafC4_3 (l : Literals) (Wk : PrimT.C4KW.KWW)
    (hDR : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.DataRerun S4 (XH L S4 T N Wk fT) (oD L S4) (hDD L S4 T N Wk fT) (g0 L S4 T N Wk fT)
        (tNt L S4 T N Wk fT) (tLt L S4 T N Wk fT) (tDt L S4 T N Wk fT))
    (hKW : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.KwDock Wk (XH L S4 T N Wk fT) (oK L S4 T N) (hKK L S4 T N Wk fT) (kInH L S4 T N Wk fT))
    (hQC : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.QCopy2 (XH L S4 T N Wk fT) (oQ L S4 T N Wk) (hQQ L S4 T N Wk fT) (srcQ L S4 T N Wk fT))
    (hobl : ∀ (fe CDs K3 D3 Kp Dp : ℕ) (F : GateFree l) (H : FinalPass.HashFr.HashFreeOk2 l F (C4LeafA.waOf l) K3 D3 Kp Dp)
      (EW : Envelope) (cW : ℕ) (W : ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1), C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0),
      F.filterErrDeg = fe → ClassLE (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) F.E →
      HashObl3 l F (C4LeafA.waOf l) K3 D3 Kp Dp H EW cW W cnw dnw Wk (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp))) :
    PrimT.C4K.HashLeafC4 l :=
  hashLeafC4_of3 l (C4LeafA.waOf l) cnw dnw (Classical.choose_spec (Classical.choose_spec PrimT.C4GateSym.needW_pb)).2
    (C3Leaf.c3ReqLeaf3 l) Wk hDR hKW hQC hobl

/-- **The c4 leaf's finish shape** (`C4Stage6.StageT = ∀ l, C4Leaf l`): the dock `C4ThrClosed.c4Leaf_of_hash` at
the HASH part, from the kept words writer, the three stage contracts' producers and the obligations. -/
noncomputable def c4Leaf_of_obl3 (Wk : PrimT.C4KW.KWW)
    (hDR : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.DataRerun S4 (XH L S4 T N Wk fT) (oD L S4) (hDD L S4 T N Wk fT) (g0 L S4 T N Wk fT)
        (tNt L S4 T N Wk fT) (tLt L S4 T N Wk fT) (tDt L S4 T N Wk fT))
    (hKW : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.KwDock Wk (XH L S4 T N Wk fT) (oK L S4 T N) (hKK L S4 T N Wk fT) (kInH L S4 T N Wk fT))
    (hQC : ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ} (L : Lay)
      (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
      (fT : ℕ), PrimT.C4KW.QCopy2 (XH L S4 T N Wk fT) (oQ L S4 T N Wk) (hQQ L S4 T N Wk fT) (srcQ L S4 T N Wk fT))
    (hobl : ∀ (l : Literals) (fe CDs K3 D3 Kp Dp : ℕ) (F : GateFree l) (H : FinalPass.HashFr.HashFreeOk2 l F (C4LeafA.waOf l) K3 D3 Kp Dp)
      (EW : Envelope) (cW : ℕ) (W : ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1), C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0),
      F.filterErrDeg = fe → ClassLE (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) F.E →
      HashObl3 l F (C4LeafA.waOf l) K3 D3 Kp Dp H EW cW W cnw dnw Wk (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp))) :
    ∀ l : Literals, PrimT.SeedFixTypes.C4Leaf l :=
  C4ThrClosed.c4Leaf_of_hash (fun l => hashLeafC4_3 l Wk hDR hKW hQC (hobl l))

end NearCubicWires.WireExponent3_5.PrimT.C4HL
