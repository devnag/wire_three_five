import Proof.Wire_3_5.Primitive.Writers.ThrCall

/-! # c4 THR block, the THR stage from the numbers machine's run (twin of `SymBig`, `sym_stage_of_big4`)

P3:2929-2941, 3011-3016, 1200, 3098-3100: `ThrBig` (the THR numbers machine's run at the capacity `cap`, the
thirty-nine words at the THR call's own numbers: `Q` the THR count, `n_T·2^w`, `2·dRow`, the free numbers
`Fp.val (thrX …)`), `thrT_mono` (the setup's cost monotone in the numbers machine's steps), **`thr_stage_of_big`**
(the links of `thr_call_run` at the call's own numbers).

Paper quantity of the main type: the THR stage's run to the call's seed word within the budget `Bd`. -/

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

/-- **The THR numbers machine's run at one call**: from the cell's entry (the THR writer's input `req.word ++ hbF`, the
data word's counts `cs`), within `cost` at capacity `cap`, the request stays on stream `0` and the thirty-nine words
hold the call's own numbers. -/
def ThrBig (Fp : FreeProg) (cr fe cap cost : ℕ) {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
    (I : PrimitiveInputs B) (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : I.StarAt n) (hbF : List Bool) (cs : List ℕ) : Prop :=
  ∃ (τ : WState (LNS 0) LNR) (c : ℕ),
    WExec cap (ThrNums.bigWT Fp cr fe)
      (CellLoopD.blankCellD 0 ((thrReq n a ha Cs carriers translation).word ++ hbF) [] 0 (Data.unaryList cs)) τ c ∧
    c ≤ cost ∧ τ.st (sk 0 0) = frame ((thrReq n a ha Cs carriers translation).word ++ hbF) ∧
    ∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean (SeedFix.thrCount alg I hs Cs)
      (SeedFix.callKh (I.starParams n hs))
      (max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
        (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)))
      (Enum.thrNT alg I hs Cs * 2 ^ wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs))
      (0 + C4Geo.dRow (I.starParams n hs) + C4Geo.dRow (I.starParams n hs))
      (Fp.val (thrX I alg Cs carriers hs))
      (derVals (SeedFix.thrCount alg I hs Cs) (SeedFix.callKh (I.starParams n hs))
        (Fp.val (thrX I alg Cs carriers hs) 0) (Fp.val (thrX I alg Cs carriers hs) 1)) j

variable (L : Lay)

/-- The THR setup's cost is monotone in the numbers machine's steps. -/
theorem thrT_mono (w : List Bool) (n CL Cd Cc n3 W ch : ℕ) (u : List Bool) {c1 c2 : ℕ} (hc : c1 ≤ c2)
    (ell d2 ρ B3 : ℕ) (Fm : C4Loop.ChildFam) (R nf : ℕ) :
    C4Wrap.wrapCost (setupT3Cost L w n CL Cd Cc n3 W ch u c1 ell d2 ρ B3) Fm R nf ≤
      C4Wrap.wrapCost (setupT3Cost L w n CL Cd Cc n3 W ch u c2 ell d2 ρ B3) Fm R nf := by
  unfold C4Wrap.wrapCost setupT3Cost cbCost bigCost
  omega

/-- **The THR stage at a call from the numbers machine's run** (`ThrBig` at `2·2^{capExp2 Cc n} + 2`). -/
theorem thr_stage_of_big {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
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
    (cost : ℕ) (hbig : ThrBig Fp cr fe (2 * 2 ^ C4Cap.capExp2 Cc n + 2) cost I alg ha Cs carriers translation hs hbF cs)
    (hkh1 : 1 ≤ SeedFix.callKh (I.starParams n hs)) (B3 dg : ℕ)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS
      ((thrReq n a ha Cs carriers translation).word ++ hbF) (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) (((Fp.val (thrX I alg Cs carriers hs)) 4)) (((Fp.val (thrX I alg Cs carriers hs)) 5))
      (C4Child.pre alg (thrR0 I hs Cs carriers translation (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0))
      (C4Child.post alg (thrR0 I hs Cs carriers translation (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0)))
    (E3 : Envelope) (K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      C4Dock.EnumOk (thrSP alg I hs Cs) (thrEnts alg I hs Cs carriers translation) (((Fp.val (thrX I alg Cs carriers hs)) 0)) (((Fp.val (thrX I alg Cs carriers hs)) 1))
        (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K (thrExprs alg I hs Cs carriers translation)
        (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      (C4Child.chR (thrR0 I hs Cs carriers translation (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0)
        (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
        (thrExprs alg I hs Cs carriers translation) (p ++ [b])).Pre alg)
    (hQp : ((Fp.val (thrX I alg Cs carriers hs)) 2) ≤ ((Fp.val (thrX I alg Cs carriers hs)) 5))
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (thrSP alg I hs Cs).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (((Fp.val (thrX I alg Cs carriers hs)) 5) + 1)
        (thrR0 I hs Cs carriers translation (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (thrR0 I hs Cs carriers translation (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg
          (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0) (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
          (thrExprs alg I hs Cs carriers translation) (p ++ [b]))) →
      C4Child.coreCost wa alg (thrR0 I hs Cs carriers translation (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0)
        (thrSP alg I hs Cs) (((Fp.val (thrX I alg Cs carriers hs)) 0)) (((Fp.val (thrX I alg Cs carriers hs)) 1)) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K
        (thrExprs alg I hs Cs carriers translation) (p ++ [b]) r ≤ Kch)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (thrSP alg I hs Cs).ell → ∀ z,
      (2 : ℤ) ^ (((Fp.val (thrX I alg Cs carriers hs)) 4) - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ ((Fp.val (thrX I alg Cs carriers hs)) 2))
    (hR : (thrFam alg I hs Cs carriers translation wa E3 (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0
      (thrEnts alg I hs Cs carriers translation) (((Fp.val (thrX I alg Cs carriers hs)) 0)) (((Fp.val (thrX I alg Cs carriers hs)) 1)) K Kch hok hpre hQp hcost).cellCost + 1 ≤ 2 ^ ((Fp.val (thrX I alg Cs carriers hs)) 6))
    (Bd : ℕ)
    (hBd : C4Wrap.wrapCost (setupT3Cost L ((thrReq n a ha Cs carriers translation).word ++ hbF) n CL Cd Cc n3
      (2 ^ C4Cap.capExp2 Cc n) ch (Data.unaryList cs) cost
      (max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
        (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)))
      (0 + C4Geo.dRow (I.starParams n hs) + C4Geo.dRow (I.starParams n hs)) (((Fp.val (thrX I alg Cs carriers hs)) 6)) B3)
      (thrFam alg I hs Cs carriers translation wa E3 (((Fp.val (thrX I alg Cs carriers hs)) 3)) (((Fp.val (thrX I alg Cs carriers hs)) 2)) 0 (((Fp.val (thrX I alg Cs carriers hs)) 4)) dg (((Fp.val (thrX I alg Cs carriers hs)) 5)) 0
        (thrEnts alg I hs Cs carriers translation) (((Fp.val (thrX I alg Cs carriers hs)) 0)) (((Fp.val (thrX I alg Cs carriers hs)) 1)) K Kch hok hpre hQp hcost) (2 ^ ((Fp.val (thrX I alg Cs carriers hs)) 6))
      (ThrFin.finCost (thrSP alg I hs Cs)
        (SeedFix.greedyBitsQ (thrSP alg I hs Cs) (SeedFix.thrStateBits alg I hs Cs carriers translation)) hbF) + 1
      ≤ Bd) :
    SeedFixTypes.Stage3Run (thrStageU3 L CL Cd Cc x3 s3 M3 Fp cr fe wa hT) Bd
      ((thrReq n a ha Cs carriers translation).word ++ hbF) (thrTape alg I hs Cs carriers translation)
      (seedWord I alg (thrReq n a ha Cs carriers translation)) := by
  obtain ⟨τ, c, hx, hc, hτ0, hτ⟩ := hbig
  have hell : 1 ≤ max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) := le_trans (by omega) (le_max_left _ _)
  have e_ell : (thrSP alg I hs Cs).ell = max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) := by
    show max 1 (max (2 * SeedFix.callKh (I.starParams n hs)) (Nat.clog 2 (SeedFix.thrCount alg I hs Cs))) = _
    rw [two_mul]
    exact max_eq_right hell
  have e_cnt : Enum.thrNT alg I hs Cs * 2 ^ wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) =
      Enum.thrNT alg I hs Cs * 2 ^ (8 + 8 * (thrSP alg I hs Cs).ell + 8 * (thrSP alg I hs Cs).kh) := by
    rw [e_ell]
    show _ = Enum.thrNT alg I hs Cs * 2 ^ (8 + 8 * (max (SeedFix.callKh (I.starParams n hs) +
      SeedFix.callKh (I.starParams n hs)) (Nat.clog 2 (SeedFix.thrCount alg I hs Cs))) +
      8 * SeedFix.callKh (I.starParams n hs))
    congr 2
    unfold wOf
    ring
  have e_uu : 2 ^ C4Geo.dRow (I.starParams n hs) * 2 ^ C4Geo.dRow (I.starParams n hs) =
      2 ^ (0 + C4Geo.dRow (I.starParams n hs) + C4Geo.dRow (I.starParams n hs)) := by rw [Nat.zero_add, pow_add]
  exact thr_call_run L I alg wa hDL CL Cd Cc x3 s3 n3 M3 Fp cr fe hT htS ha Cs carriers translation hs hbF e_hb cs hd
    τh ch hxe hτh0 hZ τ c hx hτ0 (SeedFix.thrCount alg I hs Cs) (SeedFix.callKh (I.starParams n hs)) _ _ _
    (Fp.val (thrX I alg Cs carriers hs)) _ hτ hell B3 dg hc3 E3 K Kch hok hpre hQp hcost e_ell rfl rfl rfl rfl e_cnt
    e_uu hkh1 hrange hR Bd (le_trans (Nat.add_le_add_right (thrT_mono L _ n CL Cd Cc n3 _ ch _ hc _ _ _ B3 _ _ _) 1)
      hBd)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
