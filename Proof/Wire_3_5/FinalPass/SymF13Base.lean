import Proof.Wire_3_5.FinalPass.SymF10
import Proof.Wire_3_5.FinalPass.SymF12Base
import Proof.Wire_3_5.FinalPass.SymFront3Base

/-! # SWf (the SYM words writer's flat tables), part 13: the flat part's machine and its run at a SYM request

The flat part runs on NW's bank past the front's data region: **`swfM l W F`** = the SYM front (`SymFront.frontM`: the
flat list's numbers in registers) then the four docked flat tables writers (`tailM`, part 10, the writer
`tabMP W c_r (9E₀) (CWP K₀) E₀ K₀` of part 12 on four blocks of `twW` tapes past `DT + 3`). **`swf_run`**: at a SYM
request, at a capacity above the front's need, the front's register bound and the requests, the part steps to a
state with the four circuits' flat tables words `flatWord (symListParams …) L_c` on the blocks' output tapes, the
input kept, every head and register `0`, every other stream within the bound.

Paper quantity of the main type: the call words `4·2 + c` (the list seeds' flat tables of circuit `c`, list:flatten
P3:1508-1520) at the request, on the part's output streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline NearCubicWires.BlockPlatform

/-- The front's region. -/
abbrev xFw : ℕ := DataDock.DT + 3

section Layout


end Layout

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymF
