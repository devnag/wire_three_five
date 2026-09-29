import Proof.CaseAnalysis.WeakNativeBound
import Proof.CaseAnalysis.WitnessNativePipelineBudget

/-! A hierarchy changes only one linear scale coefficient. Both source
powers below are fixed before hierarchy k, its code, and padding are chosen. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.HierarchyBudget
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open CloseoutWeakRuntime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def coefficient {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ):=
  HierarchySourceCost.coefficient source H Cpad+HierarchyStreamCost.sizeCoefficient source H Cpad+
    logCoefficient k H.coefficient+3
def scale {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad N : ℕ):=
  coefficient source H Cpad*(N+2)
def sourceBound (T : ℕ):=T^(1+HierarchySourceCost.inputExponent source+HierarchySourceCost.logExponent source)
def sizeBound (T : ℕ):=T^(1+HierarchySourceCost.inputExponent source+HierarchyStreamCost.logBase source)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.HierarchyBudget
