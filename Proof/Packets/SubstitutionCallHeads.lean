import Proof.Packets.SubstitutionOuterLoop
import Proof.Packets.SubstitutionPrepareCopies
import Proof.Packets.PhysicalProductSeek

/-! Paid cursor setup and restoration for the reusable substitution call. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def moveDrivers (d : HeadMove) := Composition.machine (PhysicalIndexReload.move (35 : Fin 44) d)
  (Composition.machine (PhysicalIndexReload.move (38 : Fin 44) d) (PhysicalIndexReload.move (43 : Fin 44) d))

def seekPorts : Fin 3→Fin 44 := ![37,38,43]
noncomputable def seek := RecoveryFocus.machine seekPorts PhysicalProductSeek.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
