import Proof.CaseAnalysis.RowsBankClear

/-! A complete polynomial call returns to the enclosing bank's erased
native ports. Every transition and sweep is paid; the growing output stays live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPolynomial
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary
open CloseoutRowsPreparationBounds CloseoutRowsPreparationFits CloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine CloseoutRowsPolynomial.machine CloseoutRowsBankClear.machine
def budget (Q C : ℕ) := CloseoutRowsDegreeLoop.budget Q C+1+CloseoutRowsBankClear.budget C

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPolynomial
