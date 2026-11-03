import Proof.Wire_3_5.Primitive.Writers.ThrG3
import Proof.Wire_3_5.FinalPass.FreeGen
import Proof.Wire_3_5.Primitive.Writers.ThrFam2
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA4
import Proof.Wire_3_5.Primitive.Writers.ThrN4

/-! # c4 THR block, the THR stage at one call (twin of `sym_call_run4`)

P3:1886-1906, 2331-2333, 3011-3016, 3034-3038, 3098-3100: the THR stage at the capacity v2 (`thrStage3_run`) at one
THR call, with the THR child family `thrFam` at the free numbers `fr` and the degree bound `dg`:
* `seedWord_thr` (definitional): the THR call's seeds are the greedy seed's samples, then the fixed hash's framed bits;
* `thrStageU3` (one machine for every call, the proof-free `famU wa`), `thr_uniform` (rfl);
* **`thr_call_run`**: the stage's run from the side conditions (the `ThrEAt3` fields), the data stage, the hash bits,
  the numbers machine's run and the links.

Paper quantity of the main type: the THR call's `seedWord` (the fixed THR seed's samples, then the hash bits). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam

/-- **The THR call's seeds** (`seedWord`, definitional): the greedy seed's samples, then the fixed hash's framed bits. -/
theorem seedWord_thr {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : I.StarAt n) :
    seedWord I alg (thrReq n a ha Cs carriers translation) =
      FinalPass.Sample.sampleWord (thrSP alg I hs Cs).kh
        (C4Iface.seedPairs (thrSP alg I hs Cs)
          (SeedFix.greedyBitsQ (thrSP alg I hs Cs) (SeedFix.thrStateBits alg I hs Cs carriers translation))) ++
      frame (List.ofFn (FinalPass.thrHashBits (I.starParams n hs)
        ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg
        (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers)
        (thrCallJ alg I hs Cs carriers))) := by
  show (if hs' : I.StarAt n then _ else []) = _
  rw [dif_pos hs]
  rfl

variable (L : Lay)

/-- **The uniform THR stage** (capacity v2): the proof-free family `famU wa`. -/
noncomputable def thrStageU3 (CL Cd Cc x3 s3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3)
    (Fp : FreeProg) (cr fe : ℕ) (wa : RepairRepresentation.WilliamsAlgorithm)
    (hT : (C4SymW.famU wa).T + 1 + 1 + 1 ≤ L.T) : SeedFixTypes.Stage3 :=
  ⟨thrXb L x3, _, thrStageM3 L CL Cd Cc x3 s3 M3 (ThrNums.bigWT Fp cr fe) (C4SymW.famU wa) (C4Pipe.PD wa) hT⟩

/-- **The THR stage at one call**, within any budget `Bd` above its steps, from the remaining side conditions (the
`ThrEAt3` fields at `fr`, `dg`), the data stage, the hash bits, the numbers machine's run and the links. -/
theorem thr_call_run {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm)
    (hDL : 16 ≤ L.D) (CL Cd Cc x3 s3 n3 : ℕ) (M3 : Machine (Data.DS + 2 + Data.DR + 1 + x3) s3)
    (Fp : FreeProg) (cr fe : ℕ) (hT : (C4SymW.famU wa).T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : I.StarAt n) (hbF : List Bool)
    (e_hb : hbF = frame (List.ofFn (FinalPass.thrHashBits (I.starParams n hs)
      ((I.starParams n hs).translationOfCodes translation) Cs carriers (I.filterParams .thr n) alg
      (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers)
      (thrCallJ alg I hs Cs carriers))))
    (cs : List ℕ)
    (hd : ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ) (J : Fin x3 → List Bool),
      Step M3 n3 (fun _ => 0)
        (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
          (Fin.addCases (Data.rawIn ((thrReq n a ha Cs carriers translation).word ++ hbF) n
            (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) (fun _ : Fin 1 => List.replicate 0 false))
          (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := x3) (motive := fun _ => List Bool)
          (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) ∧
      tout (sTape Data.sOUT) = Data.dataWord cs ∧
      tout (sTape Data.sIN) = frame ((thrReq n a ha Cs carriers translation).word ++ hbF))
    (τh : WState (LNS 0) LNR) (ch : ℕ)
    (hxe : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) ThrHB.hbXW
      (CellLoopD.blankCellD 0 ((thrReq n a ha Cs carriers translation).word ++ hbF) [] 0 []) τh ch)
    (hτh0 : τh.st (sk 0 0) = frame ((thrReq n a ha Cs carriers translation).word ++ hbF))
    (hZ : τh.st ThrHB.sZ = marks hbF)
    (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) (ThrNums.bigWT Fp cr fe)
      (CellLoopD.blankCellD 0 ((thrReq n a ha Cs carriers translation).word ++ hbF) [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame ((thrReq n a ha Cs carriers translation).word ++ hbF))
    (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)
    (hτ : ∀ j, τ.st (sk 0 (symO j)) = symClean Q kh ell cnt d2 fr dd j) (hell : 1 ≤ ell) (B3 dg : ℕ)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS
      ((thrReq n a ha Cs carriers translation).word ++ hbF) (fr 3) (fr 2) (fr 4) (fr 5)
      (C4Child.pre alg (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0))
      (C4Child.post alg (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)))
    (E3 : Envelope) (K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      C4Dock.EnumOk (thrSP alg I hs Cs) (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1)
        (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K (thrExprs alg I hs Cs carriers translation)
        (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      (C4Child.chR (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
        (thrExprs alg I hs Cs carriers translation) (p ++ [b])).Pre alg)
    (hQp : fr 2 ≤ fr 5)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (thrSP alg I hs Cs).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (fr 5 + 1)
        (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg
          (fr 5) 0) (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
          (thrExprs alg I hs Cs carriers translation) (p ++ [b]))) →
      C4Child.coreCost wa alg (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (thrSP alg I hs Cs) (fr 0) (fr 1) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K
        (thrExprs alg I hs Cs carriers translation) (p ++ [b]) r ≤ Kch)
    (e_ell : (thrSP alg I hs Cs).ell = ell) (e_kh : (thrSP alg I hs Cs).kh = kh)
    (e_Q : (thrSP alg I hs Cs).Q = Q) (e_ellQ : ell = max (kh + kh) (Nat.clog 2 Q))
    (e_dd : dd = derVals Q kh (fr 0) (fr 1))
    (e_cnt : cnt = PrimAsm.Enum.thrNT alg I hs Cs *
      2 ^ (8 + 8 * (thrSP alg I hs Cs).ell + 8 * (thrSP alg I hs Cs).kh))
    (e_uu : 2 ^ C4Geo.dRow (I.starParams n hs) * 2 ^ C4Geo.dRow (I.starParams n hs) = 2 ^ d2)
    (hkh : 1 ≤ (thrSP alg I hs Cs).kh)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (thrSP alg I hs Cs).ell → ∀ z,
      (2 : ℤ) ^ (fr 4 - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ fr 2)
    (hR : (thrFam alg I hs Cs carriers translation wa E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0
      (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1) K Kch hok hpre hQp hcost).cellCost + 1 ≤ 2 ^ fr 6)
    (Bd : ℕ)
    (hBd : C4Wrap.wrapCost (setupT3Cost L ((thrReq n a ha Cs carriers translation).word ++ hbF) n CL Cd Cc n3
      (2 ^ C4Cap.capExp2 Cc n) ch (Data.unaryList cs) c ell d2 (fr 6) B3)
      (thrFam alg I hs Cs carriers translation wa E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0
        (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1) K Kch hok hpre hQp hcost) (2 ^ fr 6)
      (ThrFin.finCost (thrSP alg I hs Cs)
        (SeedFix.greedyBitsQ (thrSP alg I hs Cs) (SeedFix.thrStateBits alg I hs Cs carriers translation)) hbF) + 1
      ≤ Bd) :
    SeedFixTypes.Stage3Run (thrStageU3 L CL Cd Cc x3 s3 M3 Fp cr fe wa hT) Bd
      ((thrReq n a ha Cs carriers translation).word ++ hbF) (thrTape alg I hs Cs carriers translation)
      (seedWord I alg (thrReq n a ha Cs carriers translation)) := by
  rw [seedWord_thr I alg ha Cs carriers translation hs, ← e_hb]
  obtain ⟨tout, m, J, h3, hO, hI⟩ := hd
  have hS := C4SymW.chFam_shape wa alg (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
    (thrSP alg I hs Cs) (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1) (PrimAsm.Enum.thrNT alg I hs Cs)
    (carriers.length + 1) K (thrExprs alg I hs Cs carriers translation) E3 Kch hok hpre hQp hcost
  have hG := thr_prefix alg I hs Cs carriers translation wa E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0
    (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1) K Kch hok hpre hQp hcost 0 hrange
  rw [C4Loop.ChildFam.src_pfx] at hG
  have hG' := UFront.frame_injective hG
  exact thrStage3_run L hDL CL Cd Cc n ((thrReq n a ha Cs carriers translation).word ++ hbF) _
    (thrTape alg I hs Cs carriers translation) (by unfold PrimRequest.word; simp only [List.append_assoc]; rfl)
    x3 s3 n3 M3 tout m J h3 cs hO hI τh ch hxe hτh0 hbF hZ _ τ c hx hτ0 Q kh ell cnt d2 fr dd hτ
    (fr 3) (fr 2) (fr 4) (fr 5) (fr 6) hell rfl rfl rfl rfl rfl rfl
    (by
      show [true] ++ List.replicate d2 true ++ [false] ++ List.replicate d2 false ++ [true] = _
      rw [NumsX.srcWord, NumsX.reps_single, NumsX.reps_single])
    (by
      show [true] ++ List.replicate (fr 6) true ++ [false] ++ List.replicate (fr 6) false ++ [true] = _
      rw [NumsX.srcWord, NumsX.reps_single, NumsX.reps_single])
    B3 _ _ hc3 _ (C4Pipe.PD wa) (thrSP alg I hs Cs) (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1)
    (PrimAsm.Enum.thrNT alg I hs Cs) _ _ hS
    ⟨e_ell, e_kh, e_Q, e_ellQ, rfl, rfl, rfl, e_dd, e_cnt, by show GF.firstPrimitive _ = _; rw [e_ell], e_uu, rfl,
      hell⟩
    hT htS hR hkh _ hG' Bd hBd

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
