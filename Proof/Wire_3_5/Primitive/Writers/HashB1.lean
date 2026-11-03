import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrCap4Base
import Proof.Wire_3_5.Primitive.Writers.HashN2
import Proof.Wire_3_5.Primitive.Writers.HashF1Base
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashB1Base


noncomputable section
set_option maxRecDepth 4096


/-! # HASH setup (A), part 4: the HASH numbers machine's run and the hash bits at one call

The HASH twins of the `thr_big_at`/`thr_hxe_at`: at a THR call, from `thr_fits2`'s call fits (`ThrFitAt`) and
`hash_fitsX`'s free-number fits at `hashX` (`HashFitX`), the HASH numbers machine `bigWTH` runs at capacity `2M + 2`
on the THR request word (the HASH stage's input, no hash suffix) (**`hash_big_at`**, `HashBig`), and the hash bits'
program runs there with an empty suffix (**`hash_hxe_at`**; the THR setup's chain is reused unchanged).
* `hashX_eq`, `HashBig`, **`hash_big_at`**, **`hash_hxe_at`**.

Paper quantity of the main type: the HASH stage's free numbers on the loop-entry words. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Small

end Small

section At
variable (l : Literals) (F : GateFree l) (Fp : FreeProg) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ}
  (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
  (translation : List ℕ)

/-- **The HASH numbers machine's run at one call** from the fits at `M`, at capacity `2M + 2`. -/
theorem hash_big_at (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) {M : ℕ}
    (hfit : ThrFitAt Fp F.cr F.filterErrDeg M (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers
      translation hs) (hfx : HashFitX Fp M (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) :
    HashBig Fp F.cr F.filterErrDeg (2 * M + 2)
      (ThrNums.hashBigCost (2 * M + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length
        (C4GateSym.needW n) ((hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD 12 0)
        (Fp.cost (2 * M + 2) (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)))
      (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers translation hs
      (hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs ++ ThrData.thrCounts Cs carriers) := by
  obtain ⟨-, -, fQ, fkk, fgs, fG, fpS, fgG, fNT, fW, fcnt, fSm, -, -, -, fd4, fl, fwd, ftr, fcP, fhn, fcs, fS,
    fT, fL, fE, fSB, fLB, fB⟩ := hfit
  obtain ⟨hF, fv, fd0, fd1, fd3⟩ := hfx
  have hwq : (thrReq n a ha Cs carriers translation).word = Data.reqW n true (ReqBridge.thrCodes Cs)
      (carriers.map Carrier.code) (RepairRepresentation.natListWord translation) := by
    have h := ReqBridge.reqW_thrReq ha Cs carriers translation []
    rw [List.append_nil, List.append_nil] at h
    exact h.symm
  obtain ⟨hk2, hdesc, henv⟩ := C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a0 ha0 hs
  have td := C4GateSym.thr_data_hyps Cs carriers ha hk2 hdesc henv (C4GateSym.needW n) le_rfl
  have hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ C4GateSym.needW n := by
    intro c hc
    unfold ReqBridge.thrCodes at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact td.2.2.2.2.2.2.2.2.2.1 i
  obtain ⟨sb1, sb2, sb3, -, sb5, sb6, -, sb8⟩ := C4SymN.star_small ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  obtain ⟨hsc, hdc, cdd, cQl, cQ, cl, ck, ccnt, cd2, c17⟩ := caps_ofT M
    (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)
    (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
    (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).seedBits)
    (Fintype.card (ThrEq ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg))
    (ThrQ.primeSum (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)))
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).b ((callInputs l F kclk coef A a0 ha0).starParams n hs).s
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).r ((callInputs l F kclk coef A a0 ha0).starParams n hs).n
    (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 0)
    (Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 1)
    fQ fkk fgs fG fpS fgG fNT fW fcnt fSm sb1 sb2 sb3 sb5 sb6 sb8 (fv 0) (fv 1) fd0 fd1 fd3 fd4 fl
  obtain ⟨τ, c, e, hcost, hsym, hrest, -⟩ := ThrNums.bigTH_spec Fp (2 * M + 2) F.cr F.filterErrDeg
    ((callInputs l F kclk coef A a0 ha0).starParams n hs) rfl
    (thrReq n a ha Cs carriers translation).word
    (ReqBridge.thrCodes Cs) (carriers.map Carrier.code)
    (RepairRepresentation.natListWord translation)
    (hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) (carriers.map (·.length))
    (ThrTab.tupleG Cs).length (C4GateSym.needW n)
    hwq (ThrData.hashNums_length _ _ _ _ _ _)
    (by rw [List.length_map]; exact hk2) (by rw [hn0, List.length_map]) hKb (by rw [List.length_append] at fwd; omega) fcP
    (fun k => SymFam.getD_le (l := hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs ++
      ThrData.thrCounts Cs carriers) (fun v hv => by have := fhn v hv; omega) k) fcs fS
    ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap
    (F.filterErrDeg * Nat.clog 2 (((callInputs l F kclk coef A a0 ha0).starParams n hs).n + 2))
    (Fintype.card (ThrEq ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg))
    (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))
    (ThrQ.primeSum (thrCutoff ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)))
    _ (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)
    (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
    (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n)
      ((callInputs l F kclk coef A a0 ha0).filterErrDeg * Ledger.Lq n)).seedBits)
    (hn1 _ _ Cs carriers hs) (hn2 _ _ Cs carriers hs) (hn4 _ _ Cs carriers hs) (hn6 _ _ Cs carriers hs) rfl rfl rfl
    (((gate0 l F).budget kclk coef A a0 ha0).capOf_pos .thr n) fT fL fE fSB fLB fB rfl
    (thrQ_link (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs hs rfl rfl) (by show 2 ≤ n; omega)
    (by omega) hsc (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)
    (hashX_eq (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs rfl) hF hdc cQl cQ cl ck
    (fun j => C4SymN.le2' (fv j)) cdd ccnt cd2 c17
  refine ⟨τ, c, e, hcost, ?_, fun j => ?_⟩
  · rw [hrest _ C4SymN.sk0_ne_symO]; exact C4SymN.blankD_st0 _ _
  · have h1 := hsym j
    rw [← thrNT_link (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs hs rfl, C4SymL.dRow_link] at h1
    exact h1

/-- **The hash bits' program at one call with an empty suffix** (the HASH stage's input), from the fits at `M`. -/
theorem hash_hxe_at (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) {M : ℕ}
    (hfit : ThrFitAt Fp F.cr F.filterErrDeg M (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers
      translation hs) :
    ∃ τh : WState (LNS 0) LNR,
      WExec (2 * M + 2) ThrHB.hbXW (CellLoopD.blankCellD 0 ((thrReq n a ha Cs carriers translation).word ++
          []) [] 0 []) τh
        (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (C4GateSym.needW n)
          translation.length ([] : List Bool).length
          (RepairRepresentation.natListWord translation).length) ∧
      τh.st (sk 0 0) = frame ((thrReq n a ha Cs carriers translation).word ++
        []) ∧
      τh.st ThrHB.sZ = marks ([]) := by
  obtain ⟨hk2, hdesc, henv⟩ := C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have td := C4GateSym.thr_data_hyps Cs carriers ha hk2 hdesc henv (C4GateSym.needW n) le_rfl
  have hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ C4GateSym.needW n := by
    intro c hc
    unfold ReqBridge.thrCodes at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact td.2.2.2.2.2.2.2.2.2.1 i
  have hKc : ∀ c ∈ carriers.map Carrier.code, natBitLength c ≤ C4GateSym.needW n := by
    intro c hc
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc
    exact td.2.2.2.2.2.2.2.2.2.2 X hX
  have fcP := hfit.fcP
  have fwd := hfit.fwd
  have ftr := hfit.ftr
  have l1 : natBitLength n + 1 < 2 ^ (natBitLength n + 1) := Nat.lt_two_pow_self
  have l5 : (ReqBridge.thrCodes Cs).length + 1 < 2 ^ ((ReqBridge.thrCodes Cs).length + 1) := Nat.lt_two_pow_self
  have l6 : (carriers.map Carrier.code).length < 2 ^ (natBitLength (carriers.map Carrier.code).length + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (carriers.map Carrier.code).length
    have h2 : Nat.log 2 (carriers.map Carrier.code).length + 1 ≤ natBitLength (carriers.map Carrier.code).length + 1 := by
      unfold natBitLength; omega
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)
  have hw := (ReqBridge.reqW_thrReq ha Cs carriers translation
    ([]))
  rw [List.length_append] at fwd
  have hnil : ([] : List Bool).length = 0 := rfl
  have q1 : 1 ≤ 2 ^ natBitLength n := Nat.one_le_two_pow
  have q2 : 1 ≤ 2 ^ natBitLength (ReqBridge.thrCodes Cs).length := Nat.one_le_two_pow
  have q3 : 1 ≤ 2 ^ natBitLength (carriers.map Carrier.code).length := Nat.one_le_two_pow
  have q4 : 1 ≤ 2 ^ (ReqBridge.thrCodes Cs).length := Nat.one_le_two_pow
  obtain ⟨τ, hx, hZ, h0, -⟩ := ThrHB.hbX_spec (2 * M + 2) n (ReqBridge.thrCodes Cs) (carriers.map Carrier.code)
    translation ([])
    (C4GateSym.needW n) hKb hKc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ftr (by omega)
  rw [hw] at hx h0
  exact ⟨τ, hx, h0, hZ⟩

end At

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap

end
