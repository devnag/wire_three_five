import Proof.Packets.PacketsPrimeService
import Proof.CaseAnalysis.FiveRowKeys

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.Count
open NearCubicWires NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.SupplierPrime NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. The value functions of the two selection-count inputs -/

/-- THR selection count (PM's `|Sel|`): `∏ |children_i|`; `0` off THR. -/
def thrSelOf (a : DecompositionAlgorithm) : Request → ℕ
  | .thr r _ _ _ => ∏ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length
  | _ => 0

/-- PM's `|Sel|` IS `thrSelOf` on THR: `card (ThresholdRows.Selection a r)`. -/
theorem thrSelOf_card (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    thrSelOf a (.thr r four L target) = Fintype.card (ThresholdRows.Selection a r) := by
  simp only [thrSelOf, ThresholdRows.Selection, Fintype.card_pi, Fintype.card_fin]

/-! ## 2. The stage -/

end
end RowsInit.Count
