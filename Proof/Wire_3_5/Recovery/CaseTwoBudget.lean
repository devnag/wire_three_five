import Proof.Wire_3_5.Recovery.CaseTwoExec
import Proof.CaseAnalysis.CaseTwoWholeBudget
import Proof.CaseAnalysis.CaseTwoExecutionBudget
import Proof.PCP.PCPPNativeSourceCost

/-! # The hybrid Case-2 costs are polynomial (P3:3769-3771; D1.6 A3d)

Realizes, for the hybrid Case 2, "There are at most `2^{O(q)}` SAT queries and local work, in addition to
`poly(T(N_a)) = 2^{O(q)}` refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall" (P3:3769-3771): the per-copy cost of
the padded whole block (`wbudget`) is at most a fixed monotone polynomial `blockEnv` of `Env(N) + q`, where
`Env(N)` is base's hierarchy envelope of the source length (`CloseoutCaseTwo.WholeBudgetHierarchy.envelope`, polynomial
in `N`); every term is charged by base's generic cost lemmas (`PCPPNativeResourceCost.descriptor_budget`,
`cache_parameter`, `PCPPNative.descriptor_length_bound`, `WholeBudget.request_source_bound`, `occurrence_bound`).

Paper quantity of the main type (`wbudget_le`): the padded Case-2 block's step bound, `2·wbudget + 4 ≤ blockEnv(Env + q)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoBudget
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole

noncomputable section

/-! ## A monotone polynomial envelope of one padded block -/



/-! ## The native producer's quantities under the hierarchy envelope -/

section Block

section Pieces

end Pieces

end Block

/-! ## The fold's capacity need and cost -/

section Fold
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun

end Fold

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoBudget
