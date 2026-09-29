import Proof.Wire_3_5.FinalPass.Close3
import Proof.Wire_3_5.FinalPass.Core18
import Proof.Wire_3_5.FinalPass.Stage5
import Proof.Wire_3_5.Foundations.OutMachineCarM2
import Proof.Wire_3_5.Primitive.Writers.SBFieldE
import Proof.Wire_3_5.UnionMachine.NumsC6

/-!
# The final pass, module stage 6

The sixth verified block of the final pass, shipped ahead of the finish: the out machine completed (P5, Gen: `outGen`
with its plain constants), the SYM size polynomial (SymSize), S6's size bounds N1–N3 (S6Sizes), the closure joins
`finalPassClose2`/`finalPassClose3` (open: the core half and the uniformity bundle), the machine-level writer contract
(CoreIfaceM) and its WM lift (CoreLiftM), the core half's machinery and assembly (Core1–Core18: `coreGen` over the four M-form writers, with its uniformity lemmas), the raw-dock helpers (SBEmit,
SBErase), SB's field phase (ModFull, SBWords, SBTau, SBFieldA–E), the carrier phase's contract and stages (CarIface,
CarDock, CarM1, CarM2), and NW's phase interface and phase (c) (NumsPh2, NumsC1–C6). The finish then ships only the pool writers' remaining
parts, the uniformity bundle and the instantiation of `finalPassClose3`. The target passes through
unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage6

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage5.StageT

def pass (h : StageT) : FinalPassStage5.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage6
