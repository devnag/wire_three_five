import Proof.CaseAnalysis.CloseoutScheduleMetadata
import Proof.CaseAnalysis.WitnessSourceCounts

/-! The weak machine owns its finite input cutoff, independently of the
later refuter onset. The actual original N is counted once and retained;
the fixed threshold and comparison are physical preprocessing calls. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.InputGuard
open LocalBitMultitape RecoveryRootRound RepairSource.CloseoutSchedule
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalSlots : Fin 2→Fin 8:=![4,5]
def compareSlots : Fin 4→Fin 8:=![4,2,6,7]
noncomputable def counted:=Composition.machine Metadata.lengthProgram Metadata.copyProgram
noncomputable def literal (cutoff : ℕ):=
  RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine (UnaryTemplate.tape cutoff))
noncomputable def compare:=RecoveryFocus.machine compareSlots MatrixBucketDimensions.Compare.machine
noncomputable def first (cutoff : ℕ):=Composition.machine counted (literal cutoff)
noncomputable def machine (cutoff : ℕ):=Composition.machine (first cutoff) compare

end NearCubicWires.RepairOrdinary.CloseoutWitness.InputGuard
