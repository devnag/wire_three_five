import Proof.CaseAnalysis.RawRowsModeDegree
import Proof.Circuits.DecompositionSourceBounds

/-! The exact existing residual-to-child substitution, specialized to the
corrected ordinary source. Its fresh output supplies the actual child bound. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierPrinter SupplierRadix
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def occurrenceExactChildren
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) : List (ExactThresholdGate q) :=
  (algorithm.output ⟨q, CompilerSemantics.nonStrictAsStrict
      (occurrences.get index).gate⟩).children

theorem actual_children_bound {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    (occurrenceExactChildren a gs i).length ≤
      a.coefficient*(q+(CompilerSemantics.nonStrictAsStrict (gs.get i).gate).encodingBits+1)^a.degree :=
  RepairOrdinary.DecompositionSource.children_bound a ⟨q,_⟩

end
end NearCubicWires.RepairSource.CloseoutRawRows
