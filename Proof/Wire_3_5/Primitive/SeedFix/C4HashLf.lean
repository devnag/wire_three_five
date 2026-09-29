import Proof.Wire_3_5.Primitive.SeedFix.C4HkJ
import Proof.Wire_3_5.Primitive.Writers.HashSetH2

/-! # The HASH part of C4Leaf ((A)): the HASH setup docked into the HASH stage at a THR call

P3:3011-3016 (the HASH stage: its setup, the loop over the hash seed's bits, the finisher), P3:2327-2336 (the greedy
choice prints the fixed hash's bits), P3:3105-3115 (the stage within the seed-fixing budget `c₄·seedClasses E₄`).
The HASH setup (`HashSetH.setupH_run`) ends in `HBank2`; the uniform HASH stage
(`C4Hk.hash_call_run`) runs from any such setup run. **`hash_at_call`** composes them at a THR call, given:
* **`HashSideAt`** (the setup's side conditions at the call: the THR fit, the HASH fits `HashFitX`, `TF2Ok`, the
  numbers machine's need, the cell's `CellFit`, and the call facts);
* **`HashStepsAt`** (**(C)**, `hash_steps_gen`: the stage's steps, with the setup's explicit cost `hashC0`,
  within `c₄·seedClasses E₄`);
* the data facts (as in the THR leaf), the three stage contracts (`DataRerun`, `KwDock`, `QCopy`), the C3 writer.

Paper quantity of the main type: the HASH stage's run at a THR call within the seed-fixing budget. -/

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

section Call
variable (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
  (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (EW : Envelope) (cW kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
  (L : Lay) (CL Cd Cc : ℕ)
  (S4 : ThrData.ThrDataStage4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
  (T : PrimThrW.PortsE.TopFrontPort3 ((gate0 l F).alg)) (N : PrimThrW.Nums4.NumsPort4 ((gate0 l F).alg) (callInputs l F kclk coef A a0 ha0).D) (Wk : PrimT.C4KW.KWW)

/-- The HASH stage's loop tapes fit behind the setup's bank. -/
theorem hroomH : hOff L S4 T N Wk + 12 + ((famUH UnionMachine.TailAsm.asmStage wa).T + 1 + 1 + 1) + (2 + 2 + 0 + 1) ≤
    3 + XH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T := by
  show _ ≤ 3 + (hOff L S4 T N Wk + (famUH UnionMachine.TailAsm.asmStage wa).T + 17)
  omega

/-- **The HASH stage at a family**: the uniform stage around the setup `M0H`. -/
noncomputable def hashStageH : SeedFixTypes.Stage3 :=
  hashStageU L (hLxH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T)
    (M0H L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T CL Cd Cc F.cr (ThrNums.bigWTH H.Fp F.cr F.filterErrDeg)) wa
    (hkTH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T) (hqTH L S4 T N Wk (famUH UnionMachine.TailAsm.asmStage wa).T)
    (hOff L S4 T N Wk) (hroomH (l := l) (F := F) (wa := wa) (kclk := kclk) (coef := coef) (A := A) (a0 := a0) (ha0 := ha0) (L := L) (S4 := S4) (T := T) (N := N) (Wk := Wk))

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4HL
