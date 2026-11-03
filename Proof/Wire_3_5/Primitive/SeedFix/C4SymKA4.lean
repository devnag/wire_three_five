import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWG

/-! # C4.K SYM, the stage at a call, v4 (capacity `2^{⌊n/8⌋ + Cc}`, any degree bound `dg`)

P3:1886-1906, 3011-3016, 3034-3038, 3098-3100: `sym_call_run3` on the setup at the capacity v2 (`symSetup_stage3`):
the same uniform machine shape (`famU wa`), the numbers machine at `2·2^{capExp2 Cc n} + 2`.

* `symStageU3`, **`sym_call_run4`**.

Paper quantity of the main type: the call's `seedWord` (the fixed SYM seed's samples). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- **The uniform SYM stage, v2** (capacity `2^{⌊n/8⌋ + Cc}`): the proof-free family `famU wa`. -/
noncomputable def symStageU3 (L : Lay) (CL Cd Cc : ℕ) (Fp : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ)
    (C : Ledger.CapParams) (wa : RepairRepresentation.WilliamsAlgorithm) (hT : (famU wa).T + 1 + 1 + 1 ≤ L.T)
    (htS : 31 ≤ L.tS) : SeedFixTypes.Stage3 :=
  ⟨L.X, _, symMachine3 L CL Cd Cc Fp cr fe ζ Cδ C (famU wa) (C4Pipe.PD wa) hT htS⟩

/-- **The SYM stage at one call**, within any budget `Bd` above its steps, from the remaining side conditions. -/
theorem sym_call_run4 {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm)
    (L : Lay) (hDL : 16 ≤ L.D) (CL Cd Cc : ℕ) (Fp : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams)
    (hT : (famU wa).T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : I.StarAt n)
    (cs : List ℕ) (cD : ℕ)
    (hd : ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ), Step Data.dataM cD (fun _ => 0)
      (Fin.addCases (Data.rawIn (symReq n a ha Cs carriers translation).word n (UnaryCalc.value L.D CL n)
        (UnaryCalc.value L.D Cd n)) (fun _ : Fin 1 => List.replicate 0 false))
      (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape Data.sOUT) = Data.dataWord cs ∧ tout (sTape Data.sIN) = frame (symReq n a ha Cs carriers translation).word)
    (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * 2 ^ C4Cap.capExp2 Cc n + 2) (bigW Fp cr fe ζ Cδ C)
      (CellLoopD.blankCellD 0 (symReq n a ha Cs carriers translation).word [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame (symReq n a ha Cs carriers translation).word) (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)
    (hτ : ∀ j, τ.st (sk 0 (symO j)) = symClean Q kh ell cnt d2 fr dd j) (hell : 1 ≤ ell) (B3 dg : ℕ)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS
      (symReq n a ha Cs carriers translation).word (fr 3) (fr 2) (fr 4) (fr 5)
      (C4Child.pre alg (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0))
      (C4Child.post alg (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)))
    (E3 : Envelope) (K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      C4Dock.EnumOk (C4Val.symSP I hs Cs carriers) (symEnts I hs Cs carriers) (fr 0) (fr 1)
        (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K (symExprs I hs Cs carriers) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
        (symExprs I hs Cs carriers) (p ++ [b])).Pre alg)
    (hQp : fr 2 ≤ fr 5)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (fr 5 + 1)
        (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) (fr 3)
          (fr 5) 0) (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
          (symExprs I hs Cs carriers) (p ++ [b]))) →
      C4Child.coreCost wa alg (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (C4Val.symSP I hs Cs carriers) (fr 0) (fr 1) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K
        (symExprs I hs Cs carriers) (p ++ [b]) r ≤ Kch)
    (e_ell : (C4Val.symSP I hs Cs carriers).ell = ell) (e_kh : (C4Val.symSP I hs Cs carriers).kh = kh)
    (e_Q : (C4Val.symSP I hs Cs carriers).Q = Q) (e_ellQ : ell = max (kh + kh) (Nat.clog 2 Q))
    (e_dd : dd = derVals Q kh (fr 0) (fr 1))
    (e_cnt : cnt = PrimAsm.Enum.symNT I hs Cs carriers *
      2 ^ (8 + 8 * (C4Val.symSP I hs Cs carriers).ell + 8 * (C4Val.symSP I hs Cs carriers).kh))
    (e_uu : 2 ^ C4Geo.dRow (I.starParams n hs) * 2 ^ C4Geo.dRow (I.starParams n hs) = 2 ^ d2)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ (fr 4 - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ fr 2)
    (hR : (C4Sym.symFam I hs Cs carriers translation wa alg E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0 (symEnts I hs Cs carriers)
      (fr 0) (fr 1) K Kch hok hpre hQp hcost).cellCost + 1 ≤ 2 ^ fr 6)
    (Bd : ℕ)
    (hBd : wrapCost (C4Cap.setupCost3 L (symReq n a ha Cs carriers translation).word n CL Cd Cc cD (Data.unaryList cs) c
      ell d2 (fr 6) B3) (C4Sym.symFam I hs Cs carriers translation wa alg E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0
        (symEnts I hs Cs carriers) (fr 0) (fr 1) K Kch hok hpre hQp hcost) (2 ^ fr 6)
      (C4Iface.sampCost (C4Val.symSP I hs Cs carriers)) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run (symStageU3 L CL Cd Cc Fp cr fe ζ Cδ C wa hT htS) Bd (symReq n a ha Cs carriers translation).word
      (symTape I hs Cs carriers) (seedWord I alg (symReq n a ha Cs carriers translation)) := by
  rw [seedWord_sym I alg ha Cs carriers translation hs]
  have hS := chFam_shape wa alg (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
    (C4Val.symSP I hs Cs carriers) (symEnts I hs Cs carriers) (fr 0) (fr 1) (PrimAsm.Enum.symNT I hs Cs carriers)
    (carriers.length + 2 * a) K (symExprs I hs Cs carriers) E3 Kch hok hpre hQp hcost
  have hG := C4Sym.sym_prefix I hs Cs carriers translation wa alg E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0
    (symEnts I hs Cs carriers) (fr 0) (fr 1) K Kch hok hpre hQp hcost 0 hrange
  rw [C4Loop.ChildFam.src_pfx] at hG
  have hG' := UFront.frame_injective hG
  exact symSetup_stage3 L hDL CL Cd Cc Fp cr fe ζ Cδ C n (symReq n a ha Cs carriers translation).word _
    (symTape I hs Cs carriers) (by unfold PrimRequest.word; simp only [List.append_assoc]; rfl) cs cD hd τ c hx hτ0 Q kh
    ell cnt d2 fr dd hτ hell B3 _ _ hc3 _ (C4Pipe.PD wa)
    (C4Val.symSP I hs Cs carriers) (symEnts I hs Cs carriers) (fr 0) (fr 1) (PrimAsm.Enum.symNT I hs Cs carriers)
    _ _ hS e_ell e_kh e_Q e_ellQ rfl rfl rfl e_dd e_cnt (by show GF.firstPrimitive _ = _; rw [e_ell]) e_uu rfl hT htS
    hR _ hG' Bd hBd

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
