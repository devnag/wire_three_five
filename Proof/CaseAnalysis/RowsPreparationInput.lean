import Proof.CaseAnalysis.RowsPreparationFits

/-! The concrete shared preparation capacity discharges the actual native
metadata and every selected initial work-tape extent. The growing output
prefix is absent from all of these bounds. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPreparationInput
open CloseoutRowsPreparationBounds CloseoutRowsPreparationFits
open LocalBitMultitape CloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsPreparationInput
