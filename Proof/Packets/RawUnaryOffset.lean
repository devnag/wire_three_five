import Proof.Hierarchy.HierarchyFixedWord
import Proof.PCP.PCPUnaryCopy
import Proof.Rows.PhysicalFocusBoundary

/-! Physically prepend a fixed unary offset, then copy the runtime raw unary
value. The literal64 instance completes the graded-window counter; both heads
are returned by the actual masked-reset program. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.RawUnaryOffset
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slot : Fin 1→Fin 2 := fun _=>1
def seed (offset : Nat) := RecoveryFocus.machine slot (HierarchyFixedWord.raw (CompareMachine.word offset))
def machine (offset : Nat) := Composition.machine (seed offset) PCPUnaryCopy.raw

def returned (offset : Nat) := MaskedReset.machine (machine offset) (fun _=>true)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.RawUnaryOffset
