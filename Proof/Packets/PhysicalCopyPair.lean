import Proof.Packets.PhysicalCopyInto

/-! Two paid resident-word copies using the same retained physical reserve.
The second source and target are required to survive the first write. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCopyPair
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

noncomputable def machine {t : Nat} (width s1 t1 s2 t2 : Fin t) :=
  Composition.machine (PhysicalCopyInto.machine width s1 t1) (PhysicalCopyInto.machine width s2 t2)

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCopyPair
