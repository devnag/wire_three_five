import Lean
import Proof.Wire_3_5.FinalPass.Stage8
import Proof.Wire_3_5.FinalPass.SymF14Base
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.Foundations.OutMachineHUBase
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Foundations.OutMachineNwBVBase
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase
import Proof.Wire_3_5.Foundations.OutMachineSwLABase
import Proof.Wire_3_5.Primitive.Writers.SBCap3Base
import Proof.Wire_3_5.Primitive.Writers.SBInstBase
import Proof.Wire_3_5.Primitive.SeedFix.NwB15Base
import Proof.Wire_3_5.Primitive.SeedFix.SBIdBase
import Proof.Wire_3_5.Primitive.SeedFix.SWt5Base
import Proof.Wire_3_5.UnionMachine.NumsG2Base
import Proof.Wire_3_5.UnionMachine.NumsW2Base
import Proof.Wire_3_5.FinalPass.SymFront6Base
import Proof.Wire_3_5.UnionMachine.NumsN4
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
import Proof.Wire_3_5.FinalPass.SymF6
import Proof.Wire_3_5.FinalPass.SymFront4Base
import Proof.Wire_3_5.Foundations.OutMachineCarGenBase
import Proof.Wire_3_5.Foundations.OutMachineCarM2
import Proof.Wire_3_5.Foundations.OutMachineDataDockW2
import Proof.Wire_3_5.Foundations.OutMachineP4
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.SBEmit
import Proof.Wire_3_5.Primitive.Writers.SBErase
import Proof.Wire_3_5.Primitive.Writers.SBFieldE
import Proof.Wire_3_5.Primitive.Writers.SBNumsF
import Proof.Wire_3_5.Primitive.Writers.SBRunBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF3
import Proof.Wire_3_5.Foundations.SwPartsTabSymW
import Proof.Wire_3_5.Foundations.SwPartsTmpl
import Proof.Wire_3_5.UnionMachine.DataDock
import Proof.Wire_3_5.UnionMachine.NumsA13Base
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh2Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base
import Proof.Wire_3_5.UnionMachine.S6SizesBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 9

The ninth verified block of the final pass: SB's arithmetic statements (`sbP1Cost`, `sbFieldCost`, `sbCap`), NW's phase
(b) `phB` over `needB`/`vLinkB` and phase (d) `phD`, and SW's parts done so far: the gate tables `swG`, the top tables
`swT` (SWt1–SWt5), the flat tables `swf` (SymF7–SymF14), the templates `swLAll` (SwLK/SwL/SwLA), the SYM front's
`FrontOutB` (SymFront5/6) and the numbers' widths, table lengths, template-length interface and post-front program
`postN`/`postRun` (NumsN1–N4); and the closure joins `finalPassClose7`–`finalPassClose10`. The target passes through
unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage9

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage8.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage8.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage9

end
