import Proof.Packets.ScalarCounterSeed
import Proof.Packets.DescendingWindowPrepare
import Proof.MachineModel.UWalkUnary

/-! Actual zero-head seed operations for the window bank. Every variable
length is read from a resident count or reserve tape; no scalar or template
is installed by a configuration equality. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def source (R n : Nat) := ZeroPadding.pad R (CompareMachine.word n)
def raw := UWalkUnary.machine false false

def copy := RecoveryBoundedTapeCopy.machine

def firstSlot : Fin 1→Fin 3 := ![0]
def up := RecoveryFocus.machine firstSlot (Completion.PhysicalDriverMoves.machine 1 .right)
def down := RecoveryFocus.machine firstSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def scalarZero := Composition.machine up (Composition.machine ScalarCounterSeed.machine down)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
