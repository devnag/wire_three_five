import Proof.CaseAnalysis.RowsRawProductFields

/-! An actual raw left/right monomial pair appends their ordered product.
The left cursor and paid log are reusable; the right cursor consumes exactly
one original monomial. Repeated variable occurrences are preserved. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductPair
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawProductFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (mark true true) leftMachine) rightMachine) (mark false false)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductPair
