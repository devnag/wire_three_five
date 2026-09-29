import Proof.CaseAnalysis.RawRowsDegree
import Proof.Supplier.RowThresholdSelections

/-! Actual symmetric rows and the corrected source's threshold-selection
row use the same occurrence-coordinate count. Multiplicity is retained. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierPrime SupplierPrinter SupplierRadix
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The repaired selection equation, with no obsolete executable decomposition. -/
def thresholdRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : RepairOrdinary.ThresholdRows.Selection a r) (L den p offset : ℕ)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L den) :
    StructuralGF2Polynomial :=
  structuralCanonicalOccurrenceCoefficientRadixRow (digits := modulusDigitCount p)
    (thresholdFourfoldOccurrences r) L den Finset.univ
    (fun i => modularCoefficientResidue (RepairOrdinary.ThresholdRows.equation a r sel) p i)
    seed p offset

end
end NearCubicWires.RepairSource.CloseoutRawRows
