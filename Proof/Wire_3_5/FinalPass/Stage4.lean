import Proof.Wire_3_5.FinalPass.S5TFoc
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.FinalPass.Stage3

/-!
# The final pass, module stage 4

The fourth verified block of the final pass: the S5 seam's THR half built so far — the prelude and
docks, the tail slots 14/15, the Scrub rework and the THR path over all eight slots
, the stage and the post-scrub erasers, the scrub layout and the focus onto S4's bank
— and the targets of the portable halves (SeamsHalves). It ships ahead of the finish
so that the finish ships only the S5-THR joins, the SYM size lemma, BridgeT, S6, the assembly, S5Core and the output machine. The
target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3046-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage4

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage3.StageT

def pass (h : StageT) : FinalPassStage3.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage4
