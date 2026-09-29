import Proof.CaseAnalysis.RowsCacheInput

/-! The actual tuple-cut bytes are precisely the common-width row's cuts.
All degree and monomial occurrences remain in their enumerated order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCutMeaning
open RepairRepresentation SupplierPipeline MatrixScoreBatch RowBinLift
open CloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degreeCuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (w j : ℕ) (rows : List (List Bool)) : List Cut :=
  (RowTupleSubsets.selected w rows.length (j+1)).map fun ds =>
    split ((-2 : ℤ)^j) (RowPowerBinLift.stack (RowCachedCoordinateBounds.width gs)
      (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten)

end NearCubicWires.RepairOrdinary.CloseoutRowsCutMeaning
