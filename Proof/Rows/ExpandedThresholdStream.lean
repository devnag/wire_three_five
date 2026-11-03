import Proof.Assembly.RowProduction
import Proof.Supplier.RowThresholdSelections

/-! Exact consumer identity for the streamed canonical mixed-radix equation.
Each selected child contributes its scaled weights and its own negative target.
The final offset is a single further constant summand. Empty supports and empty
circuit lists use the same construction. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ExpandedThresholdStream
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ThresholdCompiler
open PCJ9eff70d512234a4c_Fixed
open scoped BigOperators
noncomputable section

def block {n : Nat} (g : ExactThresholdGate n) (bits : Fin n→Bool) (factor : Int) : List (Int×Bool):=
  List.ofFn (fun j=>(factor*g.weight j,bits j))++[(-(factor*g.target),true)]

variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (sel : ThresholdRows.Selection a r)

def terms (bits : Fin (thresholdFourfoldOccurrences r).length→Bool) : List (Int×Bool):=
  (List.ofFn (fun i : Fin r.circuits.length=>i)).flatMap (fun i=>
    block ((ThresholdRows.children a (r.circuits.get i)).get (sel i))
      (fun j=>bits (thresholdCircuitEmbedding r i j))
      (equationListBase (ThresholdRows.equations a r sel)^i.val))


end
end PCJ45bee56da9f34d5a_ExpandedThresholdStream
