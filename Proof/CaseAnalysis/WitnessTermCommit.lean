import Proof.CaseAnalysis.WitnessTermRecord

/-! An accepted term updates the exact mass, retains its compact coefficient,
then clears the reusable parser. All three calls share the existing driver;
the source, mass store, width and output cursor survive the whole commit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCommit
open LocalBitMultitape RecoveryRootRound SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def mass:=TapeEmbedding.machine 1 TermMass.machine
def eraseSlots (i : Fin 725) : Fin 827:=i.castAdd 102
noncomputable def erase:=RecoveryFocus.machine eraseSlots TermRead.eraser
noncomputable def kept:=Composition.machine mass TermRecord.machine
noncomputable def machine:=Composition.machine kept erase


end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCommit
