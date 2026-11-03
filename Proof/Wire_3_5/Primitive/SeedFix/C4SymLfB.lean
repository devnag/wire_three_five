import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfA
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4SymHc
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfBBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SymLeafC4, part 2: the SYM stage's runs at a call with rows and at a degenerate call

P3:3011-3016, 3034-3038 (the child decisions and the fixed seed), #146 (c′), #159 (contract v7): at a call with rows the
branched stage runs the SYM stage on the call's own tape (`sym_plain_run`, from `SymEAt3`); at a degenerate call
(`R = 0`) it writes the padded batch (constant row per entry, `R′ = 1`) and runs the SYM stage on it with the padded
child family (`sym_deg_run`, from `SymPadEAt`); the padded batch prints the same objective (`PadEval`, C1b's
`chV_pad_eval`), so the loop fixes the same seed (`sym_prefix_pad`).

* `PadEval`, `chVal_pad`, **`sym_prefix_pad`**, **`sym_plain_run`**, **`sym_deg_run`**.

Paper quantity of the main type: the SYM stage's output at the call (its seed word) within the budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters

section Call

end Call

/-- **The SYM stage at a call with rows** (`R ≥ 1`): the branched stage runs the SYM stage on the call's tape, from
the contract's side conditions `SymEAt3`, the numbers machine's run `SymBig` and the C3 writer, within any budget above
the steps of every family whose cells fit the pad. -/
theorem sym_plain_run (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (EW : Envelope)
    (cW K3 D3 kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (C3 : C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0)
    (L : Lay) (hL : L.S3 = C3.sym) (hDL : 16 ≤ L.D) (hT : (C4SymW.famU wa).T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    (CL Cc : ℕ) (Fp : FreeProg) {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (hR1 : 1 ≤ carriers.length + 2 * a)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value L.D CL n) (dg K Kch : ℕ) (E3 : Envelope)
    (hE : C4SymW.SymEAt3 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg wa Cs carriers translation hs (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)) dg K Kch E3)
    (hload : (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 3) + (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 2) + (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 4) + (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 5) ≤ K3 * (((gate0 l F).budget kclk coef A a0 ha0).psiOf n + 1) * (n + 1) ^ D3)
    (cost : ℕ) (hbig : C4SymN.SymBig Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)
      (2 * 2 ^ C4Cap.capExp2 Cc n + 2) cost (callInputs l F kclk coef A a0 ha0) ha Cs carriers translation hs)
    (Bd : ℕ)
    (hBd : ∀ Fm : C4Loop.ChildFam, Fm.cellCost + 1 ≤ 2 ^ (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6) → Fm.bound ≤ 8 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) →
      wrapCost (C4Cap.setupCost3 L (symReq n a ha Cs carriers translation).word n CL CL Cc
          (2 * Data.coreCost a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D CL n) + 2)
          (Data.unaryList (Data.symCounts a Cs carriers)) cost (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)))
          (0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)
          (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n)))
        Fm (2 ^ (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)) (C4Iface.sampCost (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) + 1 + 0 + 20 ≤ Bd) :
    SeedFixTypes.Stage3Run (C4Pad.padStage (C4SymW.symStageU3 L CL CL Cc Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) wa hT htS)) Bd (symReq n a ha Cs carriers translation).word
      (symTape (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
      (seedWord (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg (symReq n a ha Cs carriers translation)) := by
  obtain ⟨hok, hpre, hQp, hcost, hrange, hR, hcf, h3⟩ := hE
  have hc3 := C4SymW.sym_hc3 l F EW cW K3 D3 kclk coef A a0 ha0 C3 L hL ha Cs carriers translation hcall hs
    (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)) dg h3 hcf hload
  have hd := sym_data l F kclk coef A a0 ha0 ha Cs carriers translation hcall L.D CL hWL
  have hkh1 := callKh_pos ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  have hbl : ∀ x : ℕ, x = 8 * (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell → x ≤ 8 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) := by
    intro x hx
    rw [hx]
    show 8 * max 1 (max (2 * (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) ≤ _
    omega
  refine C4K.stage3Run_mono (C4Pad.padStage_plain _ _ _ _ _
    (C4SymW.sym_stage_of_big4 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg wa L hDL CL CL Cc Fp F.cr F.filterErrDeg (gateCParams1 l).ζ
      (gateCδ1 l) (gateCap l) hT htS ha Cs carriers translation hs _ hd cost hbig hkh1 _ dg hc3 E3 K Kch hok hpre hQp
      hcost hrange hR _ le_rfl) (symTape_plain _ hs Cs carriers hR1)) ?_
  have hb := hBd _ hR (hbl _ rfl)
  omega

/-- **The SYM stage at a degenerate call** (`R = 0`, #146 (c′)): the branched stage writes the padded batch and runs the
SYM stage on it with the padded child family, from `SymPadEAt`, `PadEval`, the numbers machine's run and the C3
writer, within any budget above the steps (with the pad writer's `padCost E`) of every family whose cells fit the pad. -/
theorem sym_deg_run (he : PadEval) (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (EW : Envelope)
    (cW K3 D3 kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (C3 : C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0)
    (L : Lay) (hL : L.S3 = C3.sym) (hDL : 16 ≤ L.D) (hT : (C4SymW.famU wa).T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS)
    (CL Cc : ℕ) (Fp : FreeProg) {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (hR0 : carriers.length + 2 * a = 0)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value L.D CL n) (dg K Kch : ℕ) (E3 : Envelope)
    (hE : C4SymW.SymPadEAt (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg wa Cs carriers translation hs (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)) dg K Kch E3)
    (hload : (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 3) + (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 2) + (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 4) + (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 5) ≤ K3 * (((gate0 l F).budget kclk coef A a0 ha0).psiOf n + 1) * (n + 1) ^ D3)
    (cost : ℕ) (hbig : C4SymN.SymBig Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)
      (2 * 2 ^ C4Cap.capExp2 Cc n + 2) cost (callInputs l F kclk coef A a0 ha0) ha Cs carriers translation hs)
    (Bd : ℕ)
    (hBd : ∀ Fm : C4Loop.ChildFam, Fm.cellCost + 1 ≤ 2 ^ (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6) → Fm.bound ≤ 8 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) →
      wrapCost (C4Cap.setupCost3 L (symReq n a ha Cs carriers translation).word n CL CL Cc
          (2 * Data.coreCost a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D CL n) + 2)
          (Data.unaryList (Data.symCounts a Cs carriers)) cost (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)))
          (0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)
          (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n)))
        Fm (2 ^ (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)) (C4Iface.sampCost (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) + 1 + C4Pad.padCost ((PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) ^ 2) + 20 ≤ Bd) :
    SeedFixTypes.Stage3Run (C4Pad.padStage (C4SymW.symStageU3 L CL CL Cc Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) wa hT htS)) Bd (symReq n a ha Cs carriers translation).word
      (symTape (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
      (seedWord (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg (symReq n a ha Cs carriers translation)) := by
  obtain ⟨hok, hpre, hQp, hcost, hrange, hR, hcf, h3⟩ := hE
  have hc3 := C4SymW.sym_hc3 l F EW cW K3 D3 kclk coef A a0 ha0 C3 L hL ha Cs carriers translation hcall hs
    (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)) dg h3 hcf hload
  have hd := sym_data l F kclk coef A a0 ha0 ha Cs carriers translation hcall L.D CL hWL
  have hkh1 := callKh_pos ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  have hbl : ∀ x : ℕ, x = 8 * (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell → x ≤ 8 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) := by
    intro x hx
    rw [hx]
    show 8 * max 1 (max (2 * (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) ≤ _
    omega
  obtain ⟨τ, c, hx, hc, hτ0, hτ⟩ := hbig
  have hell : 1 ≤ (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) := le_trans (by omega) (le_max_left _ _)
  have e_ell : (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell = (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) := by
    show max 1 (max (2 * (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) = (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)))
    rw [two_mul]
    exact max_eq_right hell
  have e_cnt : (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * 2 ^ C4Set.wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) = (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * 2 ^ (8 + 8 * (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell + 8 * (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).kh) := by
    rw [e_ell]
    show _ = (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * 2 ^ (8 + 8 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + 8 * (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)))
    congr 2
    unfold C4Set.wOf
    ring
  have e_uu : 2 ^ C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) * 2 ^ C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) = 2 ^ (0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) := by
    rw [Nat.zero_add, pow_add]
  have hE0 : 1 ≤ ((PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) ^ 2) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
    (Nat.pos_iff_ne_zero.mp (PrimAsm.Enum.symNT_pos (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) (by positivity))
  have e_v : SeedFix.blockWord (C4Pad.padEnts (List.replicate ((PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) ^ 2) [])) =
      SeedFix.blockWord (C4SymW.padE (callInputs l F kclk coef A a0 ha0) Cs carriers hs) := by
    show _ = SeedFix.blockWord (SeedFix.JLink.chunk (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) 1 (C4Pad.padBatch (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers)))
    rw [C4Pad.chunk_pad _ _ ([] : List SeedFix.SExpr), C4Pad.chunk_zero]
  have e_t : symTape (callInputs l F kclk coef A a0 ha0) hs Cs carriers = SeedFix.blockWord (List.replicate ((PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) ^ 2) []) := by
    show SeedFix.blockWord (SeedFix.JLink.chunk (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (carriers.length + 2 * a)
      (PrimAsm.WriterIface.symExprs (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) = _
    rw [hR0, C4Pad.chunk_zero]
  have hS := C4SymW.chFam_shape wa (gate0 l F).alg (C4Sym.symR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 3) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 2) 0 (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 4) dg (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 5) 0) (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
    (C4SymW.padE (callInputs l F kclk coef A a0 ha0) Cs carriers hs) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) 1 K (C4SymW.padB (callInputs l F kclk coef A a0 ha0) Cs carriers hs) E3 Kch hok hpre hQp hcost
  have hG := sym_prefix_pad (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg wa Cs carriers translation hs he hR0 E3 (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 3) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 2) 0 (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 4) dg (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 5) 0 (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1) K Kch
    hok hpre hQp hcost 0 hrange
  rw [C4Loop.ChildFam.src_pfx] at hG
  have hG' := UFront.frame_injective hG
  rw [C4SymW.seedWord_sym (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers translation hs, e_t]
  refine C4K.stage3Run_mono (C4Pad.padStage_deg _ _ _ ((PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) ^ 2) hE0 _
    (C4SymW.symSetup_stage3 L hDL CL CL Cc Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) n (symReq n a ha Cs carriers translation).word _
      (SeedFix.blockWord (C4Pad.padEnts (List.replicate ((PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) * (2 ^ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) ^ 2) [])))
      (by unfold PrimRequest.word; simp only [List.append_assoc]; rfl) (Data.symCounts a Cs carriers) _ hd τ c hx hτ0
      (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) _ _ (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)) _ hτ hell _ _ _ hc3 _ (C4Pipe.PD wa) (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
      (C4SymW.padE (callInputs l F kclk coef A a0 ha0) Cs carriers hs) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) _ _ hS e_ell rfl rfl rfl rfl rfl rfl rfl e_cnt
      (by show GF.firstPrimitive _ = _; rw [e_ell]) e_uu e_v hT htS hR _ hG' _ le_rfl)) ?_
  have hw := C4SymW.wrap_mono3 L (symReq n a ha Cs carriers translation).word n CL CL Cc
    (2 * Data.coreCost a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D CL n) + 2)
    (Data.unaryList (Data.symCounts a Cs carriers)) hc (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) (0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)
    (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))
    (C4Child.chFam UnionMachine.TailAsm.asmStage wa (gate0 l F).alg (C4Sym.symR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
      (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 3) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 2) 0 (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 4) dg (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 5) 0) (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (C4SymW.padE (callInputs l F kclk coef A a0 ha0) Cs carriers hs) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) 1 K
      (C4SymW.padB (callInputs l F kclk coef A a0 ha0) Cs carriers hs) E3 Kch hok hpre hQp hcost) (2 ^ (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)) (C4Iface.sampCost (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers))
  have hb := hBd (C4Child.chFam UnionMachine.TailAsm.asmStage wa (gate0 l F).alg (C4Sym.symR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
      (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 3) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 2) 0 (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 4) dg (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 5) 0) (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (C4SymW.padE (callInputs l F kclk coef A a0 ha0) Cs carriers hs) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1) (PrimAsm.Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers) 1 K
      (C4SymW.padB (callInputs l F kclk coef A a0 ha0) Cs carriers hs) E3 Kch hok hpre hQp hcost) hR (hbl _ rfl)
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4SymLf

end
