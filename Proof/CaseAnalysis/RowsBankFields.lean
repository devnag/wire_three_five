import Proof.CaseAnalysis.RowsCapacityDriver
import Proof.CaseAnalysis.RowsPolynomial
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.CaseAnalysis.RowsRawLoad

/-! The enclosing family controller has one fixed head pattern and one
common native-port extent. Neither contains the accumulated cut prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankFields
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsPreparationBounds
open CloseoutRowsPreparationFits CloseoutRowsPreparationInput
open RepairSource.VerifierDecoding RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raised (i : Fin 113) : Bool :=
  decide (i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 ∨ i=112)

end NearCubicWires.RepairOrdinary.CloseoutRowsBankFields
