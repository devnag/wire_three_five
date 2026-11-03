import Proof.Packets.PacketsXDescendingWindowInner
import Proof.Rows.PhysicalDriverMoves

/-! The actual descending inner repeat with a retained padded count bank,
including the two paid cursor moves at its head-zero boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def slot : Fin 1→Fin 61 := ![60]
noncomputable def shift (move : HeadMove) := RecoveryFocus.machine slot
  (Completion.PhysicalDriverMoves.machine 1 move)

noncomputable def machine := Composition.machine
  (Composition.machine (shift .right) DescendingWindow.machine) (shift .left)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowReady
