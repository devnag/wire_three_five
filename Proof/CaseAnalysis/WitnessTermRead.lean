import Proof.CaseAnalysis.RowsIntegerLoad
import Proof.CaseAnalysis.WitnessMassOperands

/-! One actual term field is loaded from the canonical sum stream and
decoded in the reusable bank. The stream cursor, policy width and global
aggregate survive; the same coefficient and circuit fields remain live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loadSlots : Fin 3→Fin 725:=![722,1,723]
noncomputable def loader:=RecoveryFocus.machine loadSlots FrameLoad.machine
noncomputable def parser:=TapeEmbedding.machine 5 TermCoefficient.machine
noncomputable def machine:=Composition.machine loader parser


end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
