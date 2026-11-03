import Lean
import Proof.Wire_3_5.Primitive.Writers.HashB1
import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashB1Base


noncomputable section
set_option maxRecDepth 4096


/-! # HASH setup (A), part 5: the HASH setup's run to the SymBank part (`hash_setup_run`)

The HASH stage's setup (the `hash_call_run` form, #176 (A)) reuses the THR setup's chain `ThrSet.setupT3` (M48/M53:
the front at capacity v2, the v4 data stage, the hash bits' program, the numbers machine, the modulus words and the
C3 sub-stage, the big unary words) with the HASH numbers machine `bigWTH` (the `Fp` on `hashX`), the THR request
word without hash suffix (the HASH stage's input, so the hash bits' program sees an empty suffix), and the C3
sub-stage the writer's THR stage itself (`L.S3 = C.thr`, no strip). **`hash_setup_run`**: at a THR call, from the
fits, the data stage's premises and the C3 writer's hypotheses, the setup's run leaves on the bank the request, the
HASH tape, `1^{2^{2 dRow}}`, `1^{2^ρ}`, `PRE`/`POST` of the call's request `thrR0 … (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0`
at the HASH free numbers, the log, the masked tapes and the blank cells (the `HBank2`'s SymBank part).

Paper quantity of the main type: the HASH stage's setup (the compiler request's fixed fields, the pad, the table). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- **The HASH setup's run at a THR call** to the SymBank part of the `HBank2`. -/
theorem hash_setup_run (l : Literals) (F : GateFree l) (EW : Envelope) (cW K3 D3 kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (C3 : C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0) (L : Lay) (hL : L.S3 = C3.thr) (hDL : 16 ≤ L.D)
    (CL Cd Cc : ℕ) (Fp : FreeProg) (S4 : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap)) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation)) (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value L.D CL n)
    (hLW : UnaryCalc.value L.D CL n ≤ UnaryCalc.value L.D Cd n)
    (hcu : 2 * (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)).length + 2 * UnaryCalc.value L.D CL n ≤ 2 * UnaryCalc.value L.D Cd n)
    (hneed : S4.need n ≤ 2 * UnaryCalc.value L.D Cd n + 2)
    (hfit : ThrCap.ThrFitAt Fp F.cr F.filterErrDeg (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers translation hs)
    (hfx : ThrCap.HashFitX Fp (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) (dg : ℕ)
    (h1 : 1 ≤ (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3))
    (hcf : CompilerMachine.Pool.CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs) (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
      (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0))
    (hload : (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) + (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) + (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) + (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) ≤
      K3 * ((((gate0 l F).budget kclk coef A a0 ha0).psiOf n) + 1) * (n + 1) ^ D3) :
    ∃ (c : ℕ) (B' : Fin (3 + ThrSet.thrXb L S4.x3) → List Bool), c ≤ (ThrNums.hashBigCost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD 12 0) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs))) ∧
      Step (ThrSet.setupT3 L CL Cd Cc S4.x3 S4.s3 S4.M3 (ThrNums.bigWTH Fp F.cr F.filterErrDeg))
        (ThrSet.setupT3Cost L (thrReq n a ha Cs carriers translation).word n CL Cd Cc (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) (2 ^ PrimT.C4Cap.capExp2 Cc n) (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) translation.length ([] : List Bool).length (RepairRepresentation.natListWord translation).length)
          (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) ++ ThrData.thrCounts Cs carriers)) c (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))) (fun _ => 0)
        (PrimT.SeedFixTypes.stageIn (ThrSet.thrXb L S4.x3) (thrReq n a ha Cs carriers translation).word (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) (fun _ => 0) B' ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gP0) = frame (thrReq n a ha Cs carriers translation).word ∧ B' (liftE (ThrSet.hxb L S4.x3) L.gP1) = (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gP2) = [] ∧
      (∀ j : Fin 39, B' (liftE (ThrSet.hxb L S4.x3) (L.gW j)) = symClean (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)
        (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
        (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
          (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)))
        (Enum.thrNT (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs * 2 ^ wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))
        (0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs))
        (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs))
        (derVals (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
          ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 0) ((Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 1)) j) ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gUU) = List.replicate (2 ^ (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs))) true ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gRR) = List.replicate (2 ^ (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6)) true ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gPRE) = frame (C4Child.pre (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) dg (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0)) ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gPOST) = frame (C4Child.post (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) dg (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0)) ∧
      B' (liftE (ThrSet.hxb L S4.x3) L.gLG) = List.replicate (2 ^ (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) + 1) false ∧
      (∀ i : Fin L.N, L.maskLP i = true → B' (liftE (ThrSet.hxb L S4.x3) i) = List.replicate (2 ^ (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6)) false) ∧
      (∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B' (liftE (ThrSet.hxb L S4.x3) i) = []) ∧
      (∀ i : Fin (3 + ThrSet.thrXb L S4.x3), ThrSet.offT L S4.x3 ≤ i.val → B' i = []) := by
  obtain ⟨hk2, hdesc, he⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨hL', hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu', -, -⟩ := PrimT.C4GateSym.thr_data_hyps Cs carriers ha hk2 hdesc he
    (UnaryCalc.value L.D CL n) hWL
  have hua : (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) ++ ThrData.thrCounts Cs carriers)).length = (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)).length +
      (Data.unaryList (ThrData.thrCounts Cs carriers)).length := by
    unfold Data.unaryList
    rw [List.flatMap_append, List.length_append]
  have hcu2 : 2 * (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) ++ ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcN2 : natBitLength n + 1 ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcA2 : 2 ^ (natBitLength a + 1) ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcK2 : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcx2 : ∀ x ∈ ReqBridge.thrCodes Cs,
      2 * (RepairRepresentation.natWord x).length + 2 + n + UnaryCalc.value L.D CL n ≤ 2 * UnaryCalc.value L.D Cd n + 2 :=
    fun x hx => by have := hcx x hx; omega
  have hcy2 : ∀ y ∈ carriers.map Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + UnaryCalc.value L.D CL n ≤ 2 * UnaryCalc.value L.D Cd n + 2 :=
    fun y hy => by have := hcy y hy; omega
  obtain ⟨tout, m, J, h3, hO, hI⟩ := ThrSet.thr_hd S4 ((callInputs l F kclk coef A a0 ha0).starParams n hs) ha Cs carriers translation [] (UnaryCalc.value L.D CL n)
    (UnaryCalc.value L.D Cd n) hk2 hL' hLX h2 hcN2 hcA2 hcK2 hcx2 hcy2 hcu2 hdesc hneed
  rw [List.append_nil] at h3 hI
  obtain ⟨τh, hxe, hτh0, hZ⟩ := ThrCap.hash_hxe_at l F Fp kclk coef A a0 ha0 ha Cs carriers translation hcall hs hfit
  rw [List.append_nil] at hxe hτh0
  obtain ⟨τ, c, hx, hc, hτ0, hτ⟩ := ThrCap.hash_big_at l F Fp kclk coef A a0 ha0 ha Cs carriers translation hcall hs hfit
    hfx
  have hkh1 := PrimT.C4SymLf.callKh_pos ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  have hell : 1 ≤ (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) := le_trans (by omega) (le_max_left _ _)
  have hc3 : C3ReqIface.C3Run L.S3.M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n)) L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS
      (thrReq n a ha Cs carriers translation).word (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5)
      (C4Child.pre (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) dg (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0)) (C4Child.post (gate0 l F).alg (ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) dg (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0)) := by
    rw [hL]
    exact C3.thr_run n a ha Cs carriers translation hcall hs _ _ _ _ h1 hcf hload
  obtain ⟨B', hB, fP0, fP1, fP2, fW, -, -, fUU, fRR, fPRE, fPOST, fLG, fmask, fbl, -, fbl2⟩ :=
    ThrSet.setupT3_run L hDL CL Cd Cc n (thrReq n a ha Cs carriers translation).word _ (WriterIface.hashTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (by unfold PrimRequest.word; simp only [List.append_assoc]; rfl) S4.x3 S4.s3
      (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) S4.M3 tout m J h3 _ hO hI τh _ hxe hτh0 [] hZ _ τ c hx hτ0 _ hτ (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)))
      (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) hell rfl rfl rfl rfl rfl rfl
      (by
        show [true] ++ List.replicate (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) true ++ [false] ++ List.replicate (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) false ++ [true] = _
        rw [NumsX.srcWord, NumsX.reps_single, NumsX.reps_single])
      (by
        show [true] ++ List.replicate (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) true ++ [false] ++ List.replicate (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) false ++ [true] = _
        rw [NumsX.srcWord, NumsX.reps_single, NumsX.reps_single])
      _ _ _ hc3
  exact ⟨c, B', hc, hB, fP0, fP1, fP2, fW, fUU, fRR, fPRE, fPOST, fLG, fmask, fbl, fbl2⟩

end NearCubicWires.WireExponent3_5.PrimAsm.HashSet

end
