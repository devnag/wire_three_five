import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3

/-! # c4 THR block, the THR stage's compiler run (`hc3`)

"`alg:compiler`" (P3:1886-1906) with the fixed fields `PRE`/`POST` of the THR call's request: the THR stage's C3
sub-stage is `ThrStrip.thrC3` of the THR request writer (`C3ReqIface3.C3ReqAt3.thr`), and its run on the THR input
`thrReq.word ++ hbF` at the free numbers `h, Q', m, pr = fr 3, fr 2, fr 4, fr 5` is `thr_call_run`'s premise `hc3` at
any degree bound `dg`: from `1 ≤ h`, the THR pool's `CoefFit`, the load, and the strip's run at capacity `2·pr + 2`.

* **`thr_hc3`**.

Paper quantity of the main type: the THR call's compiler request fields `PRE`/`POST`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam

/-- **The THR stage's C3 run** (`hc3` of `thr_call_run`) from the THR request writer at the call, through the strip. -/
theorem thr_hc3 (l : Literals) (F : GateFree l) (EW : Envelope) (cW cN DN kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (C : C3ReqIface3.C3ReqAt3 l F EW cW cN DN kclk coef A a0 ha0) (L : Lay) (hL : L.S3 = ThrStrip.thrC3 C.thr)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (fr : Fin 7 → ℕ) (dg : ℕ) (h1 : 1 ≤ fr 3)
    (hcf : CompilerMachine.Pool.CoefFit (gate0 l F).alg
      (C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs)
        (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
        (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers) (fr 3) (fr 2) 0))
    (hload : fr 3 + fr 2 + fr 4 + fr 5 ≤ cN * (((gate0 l F).budget kclk coef A a0 ha0).psiOf n + 1) * (n + 1) ^ DN)
    (hbF : List Bool) (Kb : ℕ) (hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ Kb)
    (hKc : ∀ c ∈ carriers.map Carrier.code, natBitLength c ≤ Kb)
    (c1 : natBitLength n + 1 ≤ 2 * fr 5 + 2)
    (c2 : 2 ^ (natBitLength (ReqBridge.thrCodes Cs).length + 1) ≤ 2 * fr 5 + 2)
    (c3 : 2 ^ (natBitLength (carriers.map Carrier.code).length + 1) ≤ 2 * fr 5 + 2)
    (c4 : Kb + 1 ≤ 2 * fr 5 + 2) (c5 : (ReqBridge.thrCodes Cs).length ≤ 2 * fr 5 + 2)
    (c6 : (carriers.map Carrier.code).length ≤ 2 * fr 5 + 2)
    (c7 : 8 * translation.length + 2 * (RepairRepresentation.natListWord translation).length + 16 ≤ 2 * fr 5 + 2)
    (cw : ((thrReq n a ha Cs carriers translation).word ++ hbF).length ≤ 2 * fr 5 + 2) :
    C3ReqIface.C3Run L.S3.M
      (ThrStrip.thrB (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
          (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))
        (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length Kb translation.length
          hbF.length (RepairRepresentation.natListWord translation).length +
          60 * ((thrReq n a ha Cs carriers translation).word ++ hbF).length + 20)
        (fr 5) ((thrReq n a ha Cs carriers translation).word ++ hbF).length (fr 3) (fr 2) (fr 4))
      L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS ((thrReq n a ha Cs carriers translation).word ++ hbF)
      (fr 3) (fr 2) (fr 4) (fr 5)
      (C4Child.pre (gate0 l F).alg (thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
        (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0))
      (C4Child.post (gate0 l F).alg (thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
        (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)) := by
  have ew : (thrReq n a ha Cs carriers translation).word ++ hbF =
      Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Carrier.code)
        (RepairRepresentation.natListWord translation ++ hbF) := (ReqBridge.reqW_thrReq ha Cs carriers translation hbF).symm
  have ep : (thrReq n a ha Cs carriers translation).word =
      Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Carrier.code)
        (RepairRepresentation.natListWord translation) := by
    have h := ReqBridge.reqW_thrReq ha Cs carriers translation []
    rw [List.append_nil, List.append_nil] at h
    exact h.symm
  rw [ew] at cw
  obtain ⟨τ, c, hx, hc, hY, h0⟩ := ThrStrip.stripW_spec (2 * fr 5 + 2) n (ReqBridge.thrCodes Cs) (carriers.map Carrier.code)
    translation hbF Kb hKb hKc c1 c2 c3 c4 c5 c6 c7 cw
  rw [← ep] at hY
  rw [← ew] at hx h0 hc
  rw [hL]
  exact ThrStrip.thrC3_run C.thr _ _ (fr 3) (fr 2) (fr 4) (fr 5) _ _ _ _
    (C.thr_run n a ha Cs carriers translation hcall hs (fr 3) (fr 2) (fr 4) (fr 5) h1 hcf hload) τ c hx hc hY h0

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
