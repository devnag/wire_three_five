import Proof.Wire_3_5.Assembly.ThrStage1
import Proof.Wire_3_5.FinalPass.RadBW6
import Proof.Wire_3_5.UnionMachine.RadTrunc
import Proof.Wire_3_5.UnionMachine.ThrDecIface

/-!
# The thr leaf, module stage 2

The second verified block of the thr leaf, shipped ahead of its finish: the Route-B RADIX types and setup pieces
(…: RadSetupB/B2/B3, RadSpec/2/3, RadScan, RadNums, RadFields/2/P, RadDigs, RadWin, RadSeed, RadTab,
RadCnt, RadTrunc), the THR unit-chain decode contract `ThrDecFront`, and the RADIX block writer
. The finish then ships only the RADIX writer's remaining stages, the unit chain and the
assembly. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `ThrLeafJ2 l`, the THR writer of `lem:primitive` (P3:3011-3016, 3165-3175) at every
literal instance.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage2

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ThrStage1.StageT

def pass (h : StageT) : ThrStage1.StageT := h

end NearCubicWires.WireExponent3_5.ThrStage2
