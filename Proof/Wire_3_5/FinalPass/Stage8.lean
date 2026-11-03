import Lean
import Proof.Wire_3_5.FinalPass.Stage7
import Proof.Wire_3_5.Foundations.OutMachineHUBase
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase
import Proof.Wire_3_5.Primitive.Writers.SBInstBase
import Proof.Wire_3_5.UnionMachine.NumsW2Base
import Proof.Wire_3_5.FinalPass.SymFront4Base
import Proof.Wire_3_5.FinalPass.SymF6
import Proof.Wire_3_5.UnionMachine.NumsG2Base
import Proof.Wire_3_5.UnionMachine.NumsA13Base
import Proof.Wire_3_5.Primitive.SeedFix.SBIdBase
import Proof.Wire_3_5.Primitive.SeedFix.NwB15Base
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.Foundations.OutMachineDataDockW2
import Proof.Wire_3_5.Foundations.SwPartsTmpl
import Proof.Wire_3_5.Foundations.SwPartsTabSymW
import Proof.Wire_3_5.Primitive.Writers.SBRunBase
import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Proof.Wire_3_5.FinalPass.CloseBase
import Proof.Wire_3_5.FinalPass.Close2Base
import Proof.Wire_3_5.FinalPass.Core18Base
import Proof.Wire_3_5.FinalPass.Core6
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.FinalPass.CoreJ10
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
import Proof.Wire_3_5.Foundations.OutMachineCarGenBase
import Proof.Wire_3_5.Foundations.OutMachineCarM2
import Proof.Wire_3_5.Foundations.OutMachineP4
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.SBEmit
import Proof.Wire_3_5.Primitive.Writers.SBErase
import Proof.Wire_3_5.Primitive.Writers.SBFieldE
import Proof.Wire_3_5.Primitive.Writers.SBNumsF
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF3
import Proof.Wire_3_5.UnionMachine.DataDock
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh2Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base
import Proof.Wire_3_5.UnionMachine.S6SizesBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 8

The eighth verified block of the final pass: the out machine's uniformity bundle `hU4` and `finalPassClose5` (X6), the
SA writer (slots 0–3, complete) and the writer combinators, the SB writer's assembly `sbWriter` with its statements
`sbIdent`/`sbOuts`, NW's phases (a), (b), (d) and its assembly `nwOf`, the shared SYM front (`front_runA`), SW's part
types and assembly `swOf` with the parts done so far (SWg; SWf's flat-table seed loop), the data dock variants and the
raw template writer, and the final join `finalPassClose6`. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage8

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage7.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage7.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage8

end
