import Lean
import Proof.Wire_3_5.FinalPass.Stage5
import Proof.Wire_3_5.FinalPass.Close2Base
import Proof.Wire_3_5.UnionMachine.S6SizesBase
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.FinalPass.Core6
import Proof.Wire_3_5.Primitive.Writers.SBEmit
import Proof.Wire_3_5.Primitive.Writers.SBErase
import Proof.Wire_3_5.Primitive.Writers.SBFieldE
import Proof.Wire_3_5.Foundations.OutMachineCarM2
import Proof.Wire_3_5.UnionMachine.NumsPh2Base
import Proof.Wire_3_5.FinalPass.Core18Base
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Proof.Wire_3_5.FinalPass.CloseBase
import Proof.Wire_3_5.FinalPass.S5TBld
import Proof.Wire_3_5.FinalPass.S5TChABase
import Proof.Wire_3_5.FinalPass.S5TChB
import Proof.Wire_3_5.FinalPass.S5TChCBase
import Proof.Wire_3_5.FinalPass.S5TFoc
import Proof.Wire_3_5.FinalPass.S5TLay
import Proof.Wire_3_5.FinalPass.S5TLay2
import Proof.Wire_3_5.FinalPass.S5TP0Base
import Proof.Wire_3_5.FinalPass.S5TParse
import Proof.Wire_3_5.FinalPass.S5TPost
import Proof.Wire_3_5.FinalPass.S5TPost2
import Proof.Wire_3_5.FinalPass.S5TPre1
import Proof.Wire_3_5.FinalPass.S5TPre2
import Proof.Wire_3_5.FinalPass.S5TPre3
import Proof.Wire_3_5.FinalPass.S5TPre4
import Proof.Wire_3_5.FinalPass.S5TPre5
import Proof.Wire_3_5.FinalPass.S5TPre6
import Proof.Wire_3_5.FinalPass.S5TPre7
import Proof.Wire_3_5.FinalPass.S5TScrBase
import Proof.Wire_3_5.FinalPass.S5TSeed1
import Proof.Wire_3_5.FinalPass.S5TSeed2
import Proof.Wire_3_5.FinalPass.S5TSeed3
import Proof.Wire_3_5.FinalPass.S5TSt3
import Proof.Wire_3_5.FinalPass.S5TStageBase
import Proof.Wire_3_5.FinalPass.S5TTF
import Proof.Wire_3_5.FinalPass.S5TTailA
import Proof.Wire_3_5.FinalPass.S5TTailB
import Proof.Wire_3_5.FinalPass.S5TUtil
import Proof.Wire_3_5.FinalPass.S5TW6
import Proof.Wire_3_5.FinalPass.S5TWin1
import Proof.Wire_3_5.FinalPass.S5TWin2
import Proof.Wire_3_5.FinalPass.S5TZf
import Proof.Wire_3_5.FinalPass.SdCtr1
import Proof.Wire_3_5.FinalPass.SdI10Base
import Proof.Wire_3_5.FinalPass.SeamsBank2Base
import Proof.Wire_3_5.FinalPass.SeamsProg3Base
import Proof.Wire_3_5.Foundations.OutMachineP4
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF3


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 6

The sixth verified block of the final pass: the out machine completed (P5, Gen: `outGen` with its plain constants), the
SYM size polynomial (SymSize), S6's size bounds N1–N3 (S6Sizes), the closure joins `finalPassClose2`/`finalPassClose3`
(open: the core half and the uniformity bundle), the machine-level writer contract (CoreIfaceM) and its WM lift
(CoreLiftM), the core half's machinery and assembly (Core1–Core18: `coreGen` over the four M-form writers, with its
uniformity lemmas), the raw-dock helpers (SBEmit, SBErase), SB's field phase (ModFull, SBWords, SBTau, SBFieldA–E), the
carrier phase's contract and stages (CarIface, CarDock, CarM1, CarM2), and NW's phase interface and phase (c) (NumsPh2,
NumsC1–C6). The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage6

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage5.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage5.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage6

end
