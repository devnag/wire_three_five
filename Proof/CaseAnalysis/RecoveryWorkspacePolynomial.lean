import Proof.CaseAnalysis.RecoveryRowFits
import Proof.Circuits.BalancedAtomCodeLedger

/-! The original graph envelope and physical workspace stay polynomial in
the actual source length. This applies only the existing arithmetic ledger;
it imports no symbolic-machine simulation as an ordinary run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspacePolynomial
open PaddedRunnerBudgetClosure R1Leaf56BalancedAtomCodeLedger
open BoundedOracleStructuralCircuit CloseoutRecoveryWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem original_workspace
    {width bound queries clauses : ℕ → ℕ}
    (hw : SourcePoly width) (hb : SourcePoly bound)
    (hq : SourcePoly queries) (hc : SourcePoly clauses)
    (htwo : SourcePoly (fun n => 2^width n)) :
    SourcePoly (fun n => originalWorkspace (width n) (bound n) (queries n) (clauses n)) := by
  have hg := ((sourcePoly_structuralGateEnvelope hw hb hq hc htwo).add hq).add hc
  have hf := (hw.add hb).add (polyDominated_const 1)
  exact hg.add ((sourcePoly_pow hf 2).const_mul 256)

end NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspacePolynomial
