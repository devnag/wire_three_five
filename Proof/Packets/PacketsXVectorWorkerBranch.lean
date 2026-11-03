import Proof.Packets.PacketsXVectorWorkerArena
import Proof.Packets.PhysicalBitCall
import Proof.Packets.PhysicalCopyInto

/-! Both delta validity flags are read physically. A paid zeroing of the right
packet precedes the conditional provider; invalid targets therefore produce
exactly the zero polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 296) 0 26)
  (PhysicalCopyInto.machine (31 : Fin 296) 0 27)
def guarded {s : Nat} (provider : Machine 296 s) :=
  PhysicalBitCall.machine (276 : Fin 296) (PhysicalBitCall.machine (279 : Fin 296) provider)
def deltaBranch {s : Nat} (provider : Machine 296 s) := Composition.machine zeroRight (guarded provider)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorWorkerArena
