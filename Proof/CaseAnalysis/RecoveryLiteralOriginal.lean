import Proof.CaseAnalysis.RecoveryLiteralRun
import Proof.CaseAnalysis.RecoveryLiteralMeaning

/-! The complete executed literal returns the exact original compiler's
native graph, actual graph count and live output reference. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
open LocalBitMultitape SourceInterfaces RepairRepresentation BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_graph (second neg : Bool) (A : Fin 61→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (h20 : A 20=out) :
    output second neg A before ref node C out 20=out++if neg then emitted second ref else [] := by
  cases neg <;> cases second <;>
    simp [output,RecoveryBoundedLiteralNode.output,RecoveryBoundedClauseReplace.output,RecoveryBoundedClauseGate.output,kind_second,
      RecoveryBoundedClauseSelect.output,RecoveryBoundedClauseSelect.lookupOutput,RecoveryBoundedClauseSelect.target,h20]
theorem output_count (second neg : Bool) (A : Fin 61→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (h25 : A 25=List.replicate node true) :
    output second neg A before ref node C out 25=List.replicate (node+neg.toNat) true := by
  cases neg <;> cases second <;>
    simp [output,RecoveryBoundedLiteralNode.output,RecoveryBoundedClauseReplace.output,RecoveryBoundedClauseGate.output,
      RecoveryBoundedClauseSelect.output,RecoveryBoundedClauseSelect.lookupOutput,RecoveryBoundedClauseSelect.target,h25]
theorem output_reference (second neg : Bool) (A : Fin 61→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) :
    output second neg A before ref node C out (RecoveryBoundedClauseSelect.target second)=
      ZeroPadding.pad C (List.replicate (if neg then node else ref) true) := by
  cases neg <;> cases second <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
