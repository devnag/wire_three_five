import Lean
import Proof.Wire_3_5.Primitive.Writers.HashSetH1
import Proof.Wire_3_5.Primitive.Writers.HashS1
import Proof.Wire_3_5.Primitive.SeedFix.C4H2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashSetH2Base


noncomputable section
set_option maxRecDepth 4096


/-! # HASH setup (C), P3 part 2: the HASH setup's run to the `HBank2` (**`setupH_run`**)

P3:3011-3016 (the HASH stage's setup before the loop), P3:2253-2290 (the Hb printer's static words), P3:2291-2296 (the
compiler request's `1^{Q'}`): at a THR call, from the stage's entry `stageIn XH w v` (the request `w = thrReq.word`, the
HASH tape `v`), the HASH setup `M0H` (the THR setup chain, two front copies, the data-stage rerun, the HASH cell,
the kept words writer and `1^{Q'}` copy) leaves the `HBank2` at the call's words: the SymBank part (M58's
`hash_setup_run`), the 94 kept words `hb0 (hbX (hashDataOf …) (capsOf (fr 1)) 0 0)` framed on `oK + j` (T-b fed by the
HASH cell's `kwIns`), `1^{Q'}` on `oQ` (T-c from `gW 34`), the bank blank from `hOff` up. The three stage contracts
(`DataRerun`, `KwDock`, `QCopy`, PrimTC4KWT, with this dock) are hypotheses.

* `stageIn_val`, `hashTape_htWord` (the HASH tape is the kept words writer's input `htWord Fs`), `hLxH`,
  `kInH_inj`, `kInH_lt`, `extC_cases`, `extC_none`; **`setupH_run`**.

Paper quantity of the main type: the `HBank2` at the call: the HASH stage's setup exit bank (the Hb printer's static
words `KW`, the compiler request's fixed fields and `1^{Q'}`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Tape

end Tape

section Lay

section Chain

end Chain

end Lay

section Run

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.HashSetH

end
