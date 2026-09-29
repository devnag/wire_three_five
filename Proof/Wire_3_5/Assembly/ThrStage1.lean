import Proof.Wire_3_5.FinalPass.RadCaps
import Proof.Wire_3_5.FinalPass.RadPre
import Proof.Wire_3_5.Primitive.Writers.HashLeafIface4

/-!
# The thr leaf, module stage 1

The first verified block of the thr leaf, shipped ahead of its finish: the writers join and the thr leaf interface
`ThrLeafOf4`, and the RADIX stage 7 (`RadReqB.Caps` and `Pre`), whose THR side
conditions (the ThrSide chain) bring the THR mode's shared machinery. Stage 2 (`ThrStage2`) ships the
Route-B RADIX block; the finish then ships only the RADIX writer's remaining stages, the unit chain and the assembly.
The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `ThrLeafJ2 l`, the THR writer of `lem:primitive` (P3:3011-3016, 3165-3175) at every
literal instance.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage1

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.ThrLeafJ2 l

def pass (h : StageT) : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.ThrLeafJ2 l := h

end NearCubicWires.WireExponent3_5.ThrStage1
