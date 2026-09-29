import Proof.Wire_3_5.Primitive.SeedFix.C4SymND3
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA4

/-! # C4.K SYM items (c)+(i), v4: the SYM stage from the numbers machine's run at the capacity `2^{⌊n/8⌋ + Cc}`

P3:2929-2941, 3011-3016, 1200, 3098-3100: `sym_stage_of_big3` at the capacity v2: the uniform stage
`symStageU3`, `SymBig` at `2·2^{capExp2 Cc n} + 2`, the setup's cost `setupCost3` monotone in the numbers machine's steps.

* `wrap_mono3`, **`sym_stage_of_big4`**.

Paper quantity of the main type: the SYM stage's run to the call's seed word within the budget `Bd`. -/

set_option autoImplicit false

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

/-- The wrapper's cost is monotone in the numbers machine's steps (capacity v2). -/
theorem wrap_mono3 (L : Lay) (w : List Bool) (n CL Cd Cc cD : ℕ) (u : List Bool) {c1 c2 : ℕ} (hc : c1 ≤ c2)
    (ell d2 ρ B3 : ℕ) (Fm : C4Loop.ChildFam) (R nf : ℕ) :
    wrapCost (C4Cap.setupCost3 L w n CL Cd Cc cD u c1 ell d2 ρ B3) Fm R nf ≤
      wrapCost (C4Cap.setupCost3 L w n CL Cd Cc cD u c2 ell d2 ρ B3) Fm R nf := by
  unfold wrapCost C4Cap.setupCost3 Lay.midCost bigCost
  omega

/-- **The SYM stage at a call from the numbers machine's run** (`SymBig` at `2·2^{capExp C n} + 2`): the links of
`sym_call_run2` hold at the call's own numbers. -/
theorem sym_stage_of_big4 {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm)
    (L : Lay) (hDL : 16 ≤ L.D) (CL Cd Cc : ℕ) (Fp : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams)
    (hT : (famU wa).T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : I.StarAt n) (cD : ℕ)
    (hd : ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ), Step Data.dataM cD (fun _ => 0)
      (Fin.addCases (Data.rawIn (symReq n a ha Cs carriers translation).word n (UnaryCalc.value L.D CL n)
        (UnaryCalc.value L.D Cd n)) (fun _ : Fin 1 => List.replicate 0 false))
      (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape Data.sOUT) = Data.dataWord (Data.symCounts a Cs carriers) ∧ tout (sTape Data.sIN) = frame (symReq n a ha Cs carriers translation).word)
    (cost : ℕ) (hbig : C4SymN.SymBig Fp cr fe ζ Cδ C (2 * 2 ^ C4Cap.capExp2 Cc n + 2) cost I ha Cs carriers translation hs)
    (hkh1 : 1 ≤ (SeedFix.callKh (I.starParams n hs))) (B3 dg : ℕ)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS
      (symReq n a ha Cs carriers translation).word ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) (C4Child.pre alg (C4Sym.symR0 I hs Cs carriers translation ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0)) (C4Child.post alg (C4Sym.symR0 I hs Cs carriers translation ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0)))
    (E3 : Envelope) (K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      C4Dock.EnumOk (C4Val.symSP I hs Cs carriers) (symEnts I hs Cs carriers) ((Fp.val (C4SymW.symX I Cs carriers hs)) 0) ((Fp.val (C4SymW.symX I Cs carriers hs)) 1)
        (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K (symExprs I hs Cs carriers) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0) (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
        (symExprs I hs Cs carriers) (p ++ [b])).Pre alg)
    (hQp : (Fp.val (C4SymW.symX I Cs carriers hs)) 2 ≤ (Fp.val (C4SymW.symX I Cs carriers hs)) 5)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) ((Fp.val (C4SymW.symX I Cs carriers hs)) 5 + 1) (C4Sym.symR0 I hs Cs carriers translation ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0) (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers)
          (carriers.length + 2 * a) (symExprs I hs Cs carriers) (p ++ [b]))) →
      C4Child.coreCost wa alg (C4Sym.symR0 I hs Cs carriers translation ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0) (C4Val.symSP I hs Cs carriers) ((Fp.val (C4SymW.symX I Cs carriers hs)) 0) ((Fp.val (C4SymW.symX I Cs carriers hs)) 1) (PrimAsm.Enum.symNT I hs Cs carriers)
        (carriers.length + 2 * a) K (symExprs I hs Cs carriers) (p ++ [b]) r ≤ Kch)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ ((Fp.val (C4SymW.symX I Cs carriers hs)) 4 - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers) (SeedFix.symStateBits I hs Cs carriers translation z) p'.length
        (SeedFix.listNum p') < 2 ^ (Fp.val (C4SymW.symX I Cs carriers hs)) 2)
    (hR : (C4Sym.symFam I hs Cs carriers translation wa alg E3 ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0
      (symEnts I hs Cs carriers) ((Fp.val (C4SymW.symX I Cs carriers hs)) 0) ((Fp.val (C4SymW.symX I Cs carriers hs)) 1) K Kch hok hpre hQp hcost).cellCost + 1 ≤ 2 ^ (Fp.val (C4SymW.symX I Cs carriers hs)) 6)
    (Bd : ℕ)
    (hBd : wrapCost (C4Cap.setupCost3 L (symReq n a ha Cs carriers translation).word n CL Cd Cc cD (Data.unaryList (Data.symCounts a Cs carriers)) cost
      (max ((SeedFix.callKh (I.starParams n hs)) + (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers))) (0 + (C4Geo.dRow (I.starParams n hs)) + (C4Geo.dRow (I.starParams n hs))) ((Fp.val (C4SymW.symX I Cs carriers hs)) 6) B3)
      (C4Sym.symFam I hs Cs carriers translation wa alg E3 ((Fp.val (C4SymW.symX I Cs carriers hs)) 3) ((Fp.val (C4SymW.symX I Cs carriers hs)) 2) 0 ((Fp.val (C4SymW.symX I Cs carriers hs)) 4) dg ((Fp.val (C4SymW.symX I Cs carriers hs)) 5) 0
        (symEnts I hs Cs carriers) ((Fp.val (C4SymW.symX I Cs carriers hs)) 0) ((Fp.val (C4SymW.symX I Cs carriers hs)) 1) K Kch hok hpre hQp hcost) (2 ^ (Fp.val (C4SymW.symX I Cs carriers hs)) 6) (C4Iface.sampCost (C4Val.symSP I hs Cs carriers)) + 1
      ≤ Bd) :
    SeedFixTypes.Stage3Run (symStageU3 L CL Cd Cc Fp cr fe ζ Cδ C wa hT htS) Bd (symReq n a ha Cs carriers translation).word (symTape I hs Cs carriers)
      (seedWord I alg (symReq n a ha Cs carriers translation)) := by
  obtain ⟨τ, c, hx, hc, hτ0, hτ⟩ := hbig
  have hell : 1 ≤ (max ((SeedFix.callKh (I.starParams n hs)) + (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers))) := le_trans (by omega) (le_max_left _ _)
  have e_ell : (C4Val.symSP I hs Cs carriers).ell = (max ((SeedFix.callKh (I.starParams n hs)) + (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers))) := by
    show max 1 (max (2 * (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers))) = (max ((SeedFix.callKh (I.starParams n hs)) + (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers)))
    rw [two_mul]
    exact max_eq_right hell
  have e_cnt : PrimAsm.Enum.symNT I hs Cs carriers * 2 ^ wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.symCount I hs Cs carriers) =
      PrimAsm.Enum.symNT I hs Cs carriers * 2 ^ (8 + 8 * (C4Val.symSP I hs Cs carriers).ell + 8 * (C4Val.symSP I hs Cs carriers).kh) := by
    rw [e_ell]
    show _ = PrimAsm.Enum.symNT I hs Cs carriers * 2 ^ (8 + 8 * (max ((SeedFix.callKh (I.starParams n hs)) + (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers))) + 8 * (SeedFix.callKh (I.starParams n hs)))
    congr 2
    unfold wOf
    ring
  have e_uu : 2 ^ (C4Geo.dRow (I.starParams n hs)) * 2 ^ (C4Geo.dRow (I.starParams n hs)) = 2 ^ (0 + (C4Geo.dRow (I.starParams n hs)) + (C4Geo.dRow (I.starParams n hs))) := by rw [Nat.zero_add, pow_add]
  exact sym_call_run4 I alg wa L hDL CL Cd Cc Fp cr fe ζ Cδ C hT htS ha Cs carriers translation hs
    (Data.symCounts a Cs carriers) cD hd τ c hx hτ0 (SeedFix.symCount I hs Cs carriers) (SeedFix.callKh (I.starParams n hs)) (max ((SeedFix.callKh (I.starParams n hs)) + (SeedFix.callKh (I.starParams n hs))) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers))) _ _ (Fp.val (C4SymW.symX I Cs carriers hs)) _ hτ hell B3 dg hc3 E3 K Kch hok hpre hQp
    hcost e_ell rfl rfl rfl rfl e_cnt e_uu hrange hR Bd (le_trans (Nat.add_le_add_right (wrap_mono3 L _ n CL Cd Cc cD _ hc
      _ _ _ B3 _ _ _) 1) hBd)

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
