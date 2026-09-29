import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface

/-! # The C3 request writers' deliverable with a polynomial load premise

The THR and SYM pools' coefficient width `h` is `poly(n)` bits: `alg:disjoint`'s children carry the gate's weight bits,
which are bounded only by the description. So the premise `h + Q' + m + pr ≤ c_N·(ψ+1)` of `C3ReqIface.C3ReqAt` cannot hold together with `CoefFit`. This file restates the writers' contract with the
premise `h + Q' + m + pr ≤ c_N·(ψ+1)·(n+1)^{D_N}`:
* **`C3ReqAt3`**: `C3ReqIface.C3ReqAt` verbatim (its stages `C3Stage`, runs `C3Run`, fields `preW`/`postW` of
  `r0`), with that premise;
* **`C3ReqLeaf3 l`**: `C3ReqIface2.C3ReqLeaf2`'s order of choice, with `D_N` chosen with `c_N` before the floors.

Paper quantities of the main type: the compiler's fixed fields `preW`/`postW` of the call's request within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3170-3173), at a pool whose coefficients need `poly(n)` bits
(alg:disjoint). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3ReqIface3
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C3ReqIface

section At
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EW : Envelope) (cW cN DN kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The C3 request writers at one call family**, at the polynomial load premise
`h + Q' + m + pr ≤ c_N·(ψ(n) + 1)·(n+1)^{D_N}`. -/
structure C3ReqAt3 where
  sym : C3Stage
  sym_run : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n, ∀ h Q m pr : ℕ, 1 ≤ h →
      CompilerMachine.Pool.CoefFit (gate0 l F).alg
        (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.symPool Cs carriers) h Q 0) →
      h + Q + m + pr ≤ cN * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ DN →
      C3Run sym.M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n))
        sym.inS sym.hS sym.qS sym.mS sym.pS sym.preS sym.postS (symReq n a' ha' Cs carriers translation).word h Q m pr
        (preW (gate0 l F).alg (r0 ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.symPool Cs carriers) h Q 0 m 0 pr 0))
        (postW (gate0 l F).alg (r0 ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.symPool Cs carriers) h Q 0 m 0 pr 0))
  thr : C3Stage
  thr_run : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n, ∀ h Q m pr : ℕ, 1 ≤ h →
      CompilerMachine.Pool.CoefFit (gate0 l F).alg
        (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) h Q 0) →
      h + Q + m + pr ≤ cN * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ DN →
      C3Run thr.M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n))
        thr.inS thr.hS thr.qS thr.mS thr.pS thr.preS thr.postS (thrReq n a' ha' Cs carriers translation).word h Q m pr
        (preW (gate0 l F).alg (r0 ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) h Q 0 m 0 pr 0))
        (postW (gate0 l F).alg (r0 ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
          (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) h Q 0 m 0 pr 0))

end At

/-- **The C3 request writers' deliverable at the polynomial load premise**: after the numbers' ratio `c_N`, its
degree `D_N` and the endpoint exponent `fe`, the floors `E_W` and `CD_W`; for every admissible `F` above both, a
coefficient `c_W` and the writers at every clock and source work. -/
def C3ReqLeaf3 (l : Literals) : Type :=
  ∀ cN DN fe : ℕ, Σ EW : Cost.Envelope, Σ CDW : ℕ, ∀ F : Split.GateFree l, F.filterErrDeg = fe →
    PrimAsm.Plan.ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), C3ReqAt3 l F EW cW cN DN kclk coef A a ha

end NearCubicWires.WireExponent3_5.PrimAsm.C3ReqIface3
