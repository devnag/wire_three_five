import Proof.Packets.MaskConstant
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.PhysicalFocusBoundary

/-! Generate the one-monomial count in a physically allocated zero bank,
returning the actual count cursor to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalOneCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := Composition.machine (MaskConstant.countMachine true)
  (Completion.PhysicalDriverMoves.machine 1 .left)

def slots {t : Nat} (target : Fin t) : Fin 1→Fin t := fun _=>target
noncomputable def into {t : Nat} (target : Fin t) := RecoveryFocus.machine (slots target) machine

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalOneCount
