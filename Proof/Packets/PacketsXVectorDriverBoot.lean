import Proof.Amplification.RecoveryScratchErase
import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata
import Proof.Packets.PhysicalCounterCopyZero

/-! Child/parent Repeat drivers are physically copied from the population
master and incremented. The descending depth driver is copied from the actual
level counter. All three retained masters survive the boot. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def childDriver := PhysicalCounterCopy.zeroSuccessor (31 : Fin 299) 281 296
def parentDriver := PhysicalCounterCopy.zeroSuccessor (31 : Fin 299) 281 297
def depthDriver := PhysicalCounterCopy.machine (31 : Fin 299) 260 298
def bootDrivers := Composition.machine (Composition.machine childDriver parentDriver) depthDriver

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
