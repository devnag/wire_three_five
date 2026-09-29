import Proof.Wire_3_5.FinalPass.SdI8

/-! # S4 (the seeds phase), part 58: the seeds phase's overhead at a star call (P3:3170-3178)

The family's machine `M4` (the prep, the tables writer `Mw` docked, the body) on the layout `gLay E twF`, and
**`ov_ok`**: at a star call, the prep, the writer's budget `budOf` and the body's fixed steps fit
`CoF·(|fpIn|+1)^{DoF}` at the register capacity `KcF·(|fpIn|+1)^{DcF}`.

Paper quantity of the main type: the seeds phase's overhead, polynomial in the input (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

