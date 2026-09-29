import Proof.Wire_3_5.Primitive.Writers.ThrB7

/-! # c4 THR block, piece 7 part 3: the THR stage's compiler run from the contract's strip field

`thr_hc3` at the strip's premises of `ThrStripAt` (the v7 contract's `strip`) and the codes' bound
`Kb = kbT n` (`ThrSide.kbT_codes`): **`thr_hc3S`**, the consumer's form of `hc3` at a THR call.

Paper quantity of the main type: the THR call's compiler request fields `PRE`/`POST`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam

/-- **The THR stage's C3 run from the strip field** (`thr_hc3` at `hbF = hbC`, `Kb = kbT n`). -/
theorem thr_hc3S (l : Literals) (F : GateFree l) (EW : Envelope) (cW cN DN kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (C : C3ReqIface3.C3ReqAt3 l F EW cW cN DN kclk coef A a0 ha0) (L : Lay) (hL : L.S3 = ThrStrip.thrC3 C.thr)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (fr : Fin 7 → ℕ) (dg : ℕ) (h1 : 1 ≤ fr 3)
    (hcf : CompilerMachine.Pool.CoefFit (gate0 l F).alg
      (C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs)
        (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
        (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers) (fr 3) (fr 2) 0))
    (hload : fr 3 + fr 2 + fr 4 + fr 5 ≤ cN * (((gate0 l F).budget kclk coef A a0 ha0).psiOf n + 1) * (n + 1) ^ DN)
    (hS : ThrFam.ThrStripAt (fr 5) ha Cs carriers translation
      (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)) :
    C3ReqIface.C3Run L.S3.M
      (ThrStrip.thrB (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
          (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))
        (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (ThrFam.kbT n) translation.length
          (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length +
          60 * ((thrReq n a ha Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)).length + 20)
        (fr 5) ((thrReq n a ha Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)).length (fr 3) (fr 2) (fr 4))
      L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS ((thrReq n a ha Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs))
      (fr 3) (fr 2) (fr 4) (fr 5)
      (C4Child.pre (gate0 l F).alg (thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
        (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0))
      (C4Child.post (gate0 l F).alg (thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
        (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, cw⟩ := hS
  obtain ⟨hKb, hKc⟩ := ThrSide.kbT_codes l F kclk coef A a0 ha0 ha Cs carriers translation hcall
  exact thr_hc3 l F EW cW cN DN kclk coef A a0 ha0 C L hL ha Cs carriers translation hcall hs fr dg h1 hcf hload _ _
    hKb hKc c1 c2 c3 c4 c5 c6 c7 cw

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
