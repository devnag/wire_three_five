import Proof.Wire_3_5.FinalPass.Close
import Proof.Wire_3_5.FinalPass.Stage4
import Proof.Wire_3_5.Foundations.OutMachineP4
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF3

/-!
# The final pass, module stage 5

The fifth verified block of the final pass, shipped ahead of the finish: the S5 THR half's remaining joins and S4 v2
(SdR2–SdR12, Asm1/Asm2: `finalPassR`, …), the core half's writer interfaces (SymWordsIface, CoreIface;
, CORE), S6's target from N1–N3 (S6Fit), the writers' capacity lift (CoreLift), the
out machine's phases 1–4 (the output machine, … m5), and the closure join `finalPassClose`, with the
FILTER setup `fsSpec` at the walk bank. The finish then ships only the core half (coreGen and the pool writers), the
SYM size and N1–N3, the out machine's print and assembly, the uniformity bundle, and the instantiation of
`finalPassClose`. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage5

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage4.StageT

def pass (h : StageT) : FinalPassStage4.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage5
