import Proof.Wire_3_5.Assembly.ThrStage2
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF4
import Proof.Wire_3_5.Primitive.Writers.ThrDimIface
import Proof.Wire_3_5.UnionMachine.ThrUnitOf

/-!
# The thr leaf, module stage 3

The third verified block of the thr leaf, shipped ahead of its finish: the RADIX setup instance and the THR unit
machine with its measure (…: RadTrunc2 … RadBnd, RadPipeB, RadAsm0–5, RadLink/RadCall, the v2–v5
setup/unit interfaces, RadNeed/RadSetupRun, UnitG/FiltLift/ThrPipes/ThrUnitRun, ThrUnitMeas/2/3, ThrUnitOf), the THR decode front so far (…: ThrDecA–E, R1–R9, F1–F4) and the THR tail interface and its first
lemmas (ThrDimIface, ThrTail0/1). The finish then ships only the decode front's call links, the tail and
the assembly. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `ThrLeafJ2 l`, the THR writer of `lem:primitive` (P3:3011-3016, 3165-3175) at every
literal instance.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage3

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ThrStage2.StageT

def pass (h : StageT) : ThrStage2.StageT := h

end NearCubicWires.WireExponent3_5.ThrStage3
