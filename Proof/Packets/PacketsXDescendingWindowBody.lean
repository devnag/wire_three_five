import Proof.Packets.DescendingWindowCounters
import Proof.CaseAnalysis.RowsDegreeAdvance
import Proof.CaseAnalysis.RowsModeWindowScalar

/-! One physically guarded elementary block in the exact normalized-window
source order. The actual unary degree descends while its binary complement
ascends. The existing emitter retains its zero-population branch. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsModeWindowLayout CloseoutRowsModeWindowScalar

private def counterSlots : Fin 3→Fin 60 := ![48,53,51]
noncomputable def counters := RecoveryFocus.machine counterSlots DescendingWindowCounters.machine
noncomputable def body := Composition.machine summand counters

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
