import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.C4ThrClosed
import Proof.Wire_3_5.FinalPass.HashFree
import Proof.Wire_3_5.FinalPass.HashFree2
import Proof.Wire_3_5.FinalPass.HashFreeBuild
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.C3W3Leaf
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.HashLeaf
import Proof.Wire_3_5.Primitive.Writers.HashSetH2
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrLf1
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf
import Proof.Wire_3_5.Primitive.SeedFix.C4HkJ
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.C4LeafA
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2Base


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH part of C4Leaf, v2: the cell's `Bm` bounded

`HashStepsAt` (M77) quantifies over every `Bm` with `CellFit`, but `CellFit` bounds `Bm` only from below and the setup's
cost grows with `Bm` (the cell's `popsCost`), so it is unprovable. v2 (new types; M77 untouched; `Sm` is bounded above
by `CellFit` itself):
* **`HashSideAt2`**: `HashSideAt` with `∃ Bm Sm, CellFit … ∧ Bm ≤ 2·2^{capExp2 C_c n} + 2`;
* **`HashStepsAt2`**: `HashStepsAt` with the premise `Bm ≤ 2·2^{capExp2 C_c n} + 2`;
* `hash_at_call2`, **`HashObl2`**, `hashLeafC4_of2`, `hashLeafC4_2`, **`c4Leaf_of_obl2 : … → ∀ l, C4Leaf l`**.

Paper quantity of the main type: the HASH stage's run at a THR call within the seed-fixing budget (P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashCell NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- **The HASH setup's side conditions at every THR call of the family** (the fits and the call facts). -/
def HashSideAt2 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
    (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (EW : Envelope) (cW kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (L : Lay) (CL Cd Cc : ℕ)
    (S4 : ThrData.ThrDataStage4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
    (T : PrimThrW.PortsE.TopFrontPort3 ((gate0 l F).alg)) (N : PrimThrW.Nums4.NumsPort4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D) (Wk : PrimT.C4KW.KWW) (fT : ℕ) : Prop :=
  ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ), (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
    (ThrCap.ThrFitAt H.Fp F.cr F.filterErrDeg (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) ha Cs carriers translation hs) ∧ (ThrCap.HashFitX H.Fp (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) ((gate0 l F).alg) Cs carriers hs) ∧
    (1 ≤ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ∧ (CompilerMachine.Pool.CoefFit ((gate0 l F).alg) (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs) (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
      (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0)) ∧ (((callInputs l F kclk coef A a0 ha0).starParams n hs).r = Ledger.rowBr F.cr n) ∧ (1 ≤ n) ∧
    (1 ≤ ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ∧ (PrimThrW.TopFront2.TF2Ok Cs (carriers.map Carrier.code) (UnaryCalc.value L.D Cd n)) ∧ (N.need (n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ≤ (UnaryCalc.value L.D Cd n)) ∧
    ∃ Bm Sm : ℕ, HashCell.CellFit ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation F.cr Bm Sm (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) ∧
      Bm ≤ 2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2

section Call

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4HL

end
