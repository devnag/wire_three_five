import Lean
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase
import Proof.Wire_3_5.Primitive.SeedFix.C4Geo
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # The pool-geometry writers' interface on the request word (restates PA's GeoIface)

P3:1188-1216 (star:partition: the halves, the code basis `φ`, the coset offset, the corners) and P3:1655-1664,
1709-1737 (alg:pullback, alg:separable-printer): the C3 compiler of a call reads the pool's geometry as fields
(`PrimT.C4Geo`). The writers read the call's request word, "The algorithm receives polynomial-bit integer circuit
descriptions" (P3:3119-3120), in the writers' port convention (`WriterIfaceJ.WriterRun`: `frame req.word` kept on
`inS`, the field on `outS`, every head at `0`, residues within the budget), at every call of the family
(`P = I.starParams n hs`, `σ = P.translationOfCodes req.translation`).

The same six structures as PA's `GeoIface` with the input `req.word` in place of `req.word ++ sfx`: an arbitrary suffix
makes the type unsatisfiable (every front unframes its whole input while the budget does not depend on the
suffix), and the consumer (the c4 per-call setup) hands each writer a fresh `frame req.word`.

* **`FlipsWriterAt`** (`C4Geo.flipsField P σ`, the selection class);
* **`ColsWriterAt`** (`C4Geo.colsField P`), **`SideWriterAt`** (`C4Geo.sideField P`), **`WidthWriterAt`**
  (`1^(C4Geo.width P)`) (the preprocessing class);
* **`GateSymWriterAt`**, **`GateThrWriterAt`** (`C4Geo.gateField` of `Records.symPool Cs carriers` /
  `Records.thrPool P Cs carriers`, the preprocessing class);
* `GeoWritersAt` and **`GeoLeaf`** in `SeedFixLeaf`'s order of choice (`fe`, then the floors `E_G`, then `F`, then
  `c_G`).

Paper quantities of the main types: the flip patterns (the corners `c+u+v`, `c+u`, `c+v`, `c` of star:delta at the coset
offset, P3:1224), the columns of `φ` (the Hamming code's basis, P3:1212-1216), the halves (P3:1213-1215), the pool's
gates (P3:1655-1664). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.GeoIface2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ

section Geo
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The columns writer**: `frame req.word ↦ C4Geo.colsField P`, within the preprocessing class. -/
structure ColsWriterAt extends WriterStage where
  ready : ∀ (req : PrimRequest), (callInputs l F kclk coef A a ha).Call req →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt req.n,
      WriterRun M (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
          (((gate0 l F).budget kclk coef A a ha).psiOf req.n)) inS outS req.word
        (PrimT.C4Geo.colsField ((callInputs l F kclk coef A a ha).starParams req.n hs))

/-- **The halves writer**: `frame req.word ↦ C4Geo.sideField P`, within the preprocessing class. -/
structure SideWriterAt extends WriterStage where
  ready : ∀ (req : PrimRequest), (callInputs l F kclk coef A a ha).Call req →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt req.n,
      WriterRun M (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
          (((gate0 l F).budget kclk coef A a ha).psiOf req.n)) inS outS req.word
        (PrimT.C4Geo.sideField ((callInputs l F kclk coef A a ha).starParams req.n hs))

/-- **The width writer**: `frame req.word ↦ 1^(C4Geo.width P)`, within the preprocessing class. -/
structure WidthWriterAt extends WriterStage where
  ready : ∀ (req : PrimRequest), (callInputs l F kclk coef A a ha).Call req →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt req.n,
      WriterRun M (cG * classBound EG .preprocessing req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
          (((gate0 l F).budget kclk coef A a ha).psiOf req.n)) inS outS req.word
        (List.replicate (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) true)

/-- **The SYM gate-frame writer**: `frame (symReq …).word ↦ C4Geo.gateField (Records.symPool Cs carriers)`. -/
structure GateSymWriterAt extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ _ : (callInputs l F kclk coef A a ha).StarAt n,
      WriterRun M (cG * classBound EG .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n)) inS outS
        (symReq n a' ha' Cs carriers translation).word
        (PrimT.C4Geo.gateField (Records.symPool Cs carriers))

/-- **The THR gate-frame writer**: `frame (thrReq …).word ↦ C4Geo.gateField (Records.thrPool P Cs carriers)`. -/
structure GateThrWriterAt extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      WriterRun M (cG * classBound EG .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n)) inS outS
        (thrReq n a' ha' Cs carriers translation).word
        (PrimT.C4Geo.gateField (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers))

end Geo

end NearCubicWires.WireExponent3_5.PrimT.GeoIface2

end
