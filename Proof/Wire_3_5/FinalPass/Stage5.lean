import Lean
import Proof.Wire_3_5.FinalPass.Stage4
import Proof.Wire_3_5.FinalPass.CloseBase
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF3
import Proof.Wire_3_5.Foundations.OutMachineP4
import Proof.Wire_3_5.FinalPass.AssemblyDock2
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
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 5

The fifth verified block of the final pass: the S5 THR half's remaining joins and S4 v2 (SdR2–SdR12, Asm1/Asm2:
`finalPassR` …), the core half's writer interfaces (SymWordsIface, CoreIface;, CORE), S6's target from N1–N3 (S6Fit),
the writers' capacity lift (CoreLift), the out machine's phases 1–4 (X6 … m5), and the closure join `finalPassClose`,
with the FILTER setup `fsSpec` at the walk bank. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage5

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage4.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage4.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage5

end
