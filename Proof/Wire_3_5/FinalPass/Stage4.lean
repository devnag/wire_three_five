import Lean
import Proof.Wire_3_5.FinalPass.Stage3
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
import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Proof.Wire_3_5.FinalPass.SeamsBank2Base
import Proof.Wire_3_5.FinalPass.SeamsProg3Base
import Proof.Wire_3_5.FinalPass.SdCtr1
import Proof.Wire_3_5.FinalPass.SdI10Base
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 4

The fourth verified block of the final pass: the S5 seam's THR half built so far (C1b) — the prelude and docks, the tail
slots 14/15, the Scrub rework and the THR path over all eight slots, the stage and the post-scrub erasers, the scrub
layout and the focus onto S4's bank — and the targets of the portable halves (SeamsHalves). The target passes through
unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3046-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage4

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage3.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage3.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage4

end
