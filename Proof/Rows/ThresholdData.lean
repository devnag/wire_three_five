import Proof.Rows.FourfoldPowerMeaning
import Proof.Rows.NativeFlagsMeaning

/-! One actual THR request supplies the same selected children to canonical
base construction and to physical coefficient production. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace PCJ45bee56da9f34d5a_ThresholdData
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
noncomputable section

def data (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r):Data where
 count:=r.circuits.length
 arity i:=(r.circuits.get i).top.support.card
 gates i:=ThresholdRows.children a (r.circuits.get i)
 selected:=sel
 count_le:=four

def base (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r):Nat:=
 1+(data a r four sel).values.sum

end
end PCJ45bee56da9f34d5a_ThresholdData
