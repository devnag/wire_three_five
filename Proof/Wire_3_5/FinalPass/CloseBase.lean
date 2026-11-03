import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Proof.Wire_3_5.FinalPass.Asm1Base
import Proof.Wire_3_5.FinalPass.SdR10Base
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Proof.Wire_3_5.Primitive.Writers.S6FitBase
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.WalkStage
import Proof.Wire_3_5.Foundations.OutMachineP3

/-!
# The final pass's closure join

The finalpass leaf's finish term, stated from EXACTLY the producers still open at 09-28, with every other
argument supplied by verified code: the FILTER setup `fsSpec walkBank` (C6, union-machine), the out machine's phases
`ph1`/`ph2`/`ph3` (X6/m4) and `ph6`, and S6's target `s6Target` (PA2). The open
producers, one binder each:

* `hS`: the SYM size polynomial;
* `mCore`, `core`: the core half (`coreGen` over the pool writers SA/SB/NW/SW);
* `ph4`, `ph5`, `outOf`: the out machine's exact divisions, print and assembly (X6);
* `h1`, `h2`, `h3`: S6's size bounds N1–N3 (`PrimAsm.S6Fit`);
* `hU`: the uniformity bundle at these parts (the assembly).

The finish instantiates `finalPassClose` at the producers once they are verified, so the final join is already
checked. Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive`
(P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- The FILTER setup at the walk bank (both verified). -/
noncomputable abbrev F5c : PrimAsm.FiltSetup.FiltSetupSpec5 UnionMachine.WalkStage.walkBank :=
  UnionMachine.FsSpec.fsSpec UnionMachine.WalkStage.walkBank

end NearCubicWires.WireExponent3_5.FinalPass.Close
