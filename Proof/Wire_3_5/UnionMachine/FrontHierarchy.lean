import Proof.Wire_3_5.UnionMachine.PlanBase
import Proof.CaseAnalysis.HierarchyRequest
import Proof.CaseAnalysis.CaseTwoHierarchyFrame
import Proof.Hierarchy.HierarchySourceConstructor

/-! # C6 front, U2b: the hierarchy request word (P3:3632-3653)

Realizes the input of "Apply the outer PCP to `H`" (P3:3632-3653) as the union's front computes it: the hierarchy
source constructor's input `hierarchyInput H ⟨N, x⟩ = frame x ++ frame (H.time N).bits` (the framed refuter input and
the hierarchy clock in binary), framed once more for the compound native input of the PCPP source
(`PCPPNativeInputFields.word`, the padded source). Two base machines, docked:
* `CloseoutHierarchyRequest.machine kclk C` (`request_run`): from `frame x`, `frame x ++ frame (C·(N^{kclk+2}+1)).bits`;
* `CloseoutCaseTwo.HierarchyFrame.machine` (`frame_run`): from that word, its frame.

Main statement: **`hier_ready`**: a ready run from the framed input to `frame (hierarchyInput H ⟨N, x⟩)` on `hOut`, at
the explicit cost `hierCost`. Paper quantity: the hierarchy's source request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontHierarchy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

variable (k : ℕ)

/-- The request machine's tapes. -/
noncomputable abbrev rT : ℕ := RepairSource.CloseoutHierarchyRequest.tapes k

/-- The layout: the request machine's tapes, then five for the framing machine. -/
noncomputable abbrev HT : ℕ := rT k + 5


end NearCubicWires.WireExponent3_5.UnionMachine.FrontHierarchy
