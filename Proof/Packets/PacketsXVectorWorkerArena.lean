import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata
import Proof.Amplification.RecoveryScratchErase

/-! Concrete 296-tape numeric arena. All window and delta scalar masters are
outside the private arithmetic work, and the cleanup is an actual parallel
R-cell overwrite with retained capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open RecoveryRootRound
noncomputable section

def windowSlots : Fin 13→Fin 296 := ![264,266,267,268,295,32,260,269,270,152,271,151,31]
def windowMachine := RecoveryFocus.machine windowSlots GradedWindow.reusable

/-- Inputs n,W,parent,child,u are retained on150,152,259,258,183.
The outputs offset,twice-W,target are produced directly on180,181,182;
276 and279 hold the actual lower and upper validity bits. -/
def metadataSlots : Fin 25→Fin 296 :=
  ![150,152,259,258,183,264,265,266,267,268,269,180,181,270,271,272,273,274,275,276,277,182,278,279,280]
def metadataMachine := RecoveryFocus.machine metadataSlots DeltaMetadata.machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
