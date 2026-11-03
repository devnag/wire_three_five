import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SYM item (d): the compiler request writer's run at the SYM stage (`hc3`)

"`alg:compiler`" (P3:1886-1906) with the fixed fields `PRE`/`POST` of the call's request (P3:3108, 3170-3173): the
SYM stage's C3 sub-stage `L.S3` is the SYM request writer (`C3ReqIface3.C3ReqAt3.sym`), and its run at the free
numbers `h, Q', m, pr = fr 3, fr 2, fr 4, fr 5` is `sym_call_run3`'s premise `hc3` at ANY degree bound `dg` (the
fields do not read `d`, `C3ReqIface.preW_irrel`): from `1 ≤ h`, the pool's `CoefFit` (SymEAt3) and the load
`h + Q' + m + pr ≤ c_N(ψ + 1)(n + 1)^{D_N}` (SymFreeOk4's `c3_le` at `c_N = K3`, `D_N = D3`).

* **`sym_hc3`**.

Paper quantity of the main type: the SYM call's compiler request fields `PRE`/`POST` within the preprocessing class. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- **The SYM stage's C3 run** (`hc3` of `sym_call_run3`) from the SYM request writer at the call. -/
theorem sym_hc3 (l : Literals) (F : GateFree l) (EW : Envelope) (cW cN DN kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (C : C3ReqIface3.C3ReqAt3 l F EW cW cN DN kclk coef A a0 ha0) (L : Lay) (hL : L.S3 = C.sym)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (fr : Fin 7 → ℕ) (dg : ℕ) (h1 : 1 ≤ fr 3)
    (hcf : CompilerMachine.Pool.CoefFit (gate0 l F).alg
      (C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs)
        (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
        (Records.symPool Cs carriers) (fr 3) (fr 2) 0))
    (hload : fr 3 + fr 2 + fr 4 + fr 5 ≤ cN * (((gate0 l F).budget kclk coef A a0 ha0).psiOf n + 1) * (n + 1) ^ DN) :
    C3ReqIface.C3Run L.S3.M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
        (((gate0 l F).budget kclk coef A a0 ha0).psiOf n))
      L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS (symReq n a ha Cs carriers translation).word
      (fr 3) (fr 2) (fr 4) (fr 5)
      (C4Child.pre (gate0 l F).alg (C4Sym.symR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
        (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0))
      (C4Child.post (gate0 l F).alg (C4Sym.symR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation
        (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)) := by
  rw [hL]
  exact C.sym_run n a ha Cs carriers translation hcall hs (fr 3) (fr 2) (fr 4) (fr 5) h1 hcf hload

end NearCubicWires.WireExponent3_5.PrimT.C4SymW

end
