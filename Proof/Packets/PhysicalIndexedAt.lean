import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.VectorCounterDecrement
import Proof.Rows.PhysicalFocusBoundary

/-! Counted physical loops over an existing arena counter. The chosen counter
is incremented by the machine after every worker call; no separate logical
index is substituted for its resident tape. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexedAt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def advance {t : Nat} (port : Fin t) := RecoveryFocus.machine (fun _ : Fin 1=>port) VectorCounter.increment
def body {t s : Nat} (port : Fin t) (worker : Machine t s) := Composition.machine worker (advance port)
def machine {t s : Nat} (port : Fin t) (worker : Machine t s) := RepeatMachine.machine (body port worker) (fun _ _=>true)

def retreat {t : Nat} (port : Fin t) := RecoveryFocus.machine (fun _ : Fin 1=>port) VectorCounter.decrement
def downBody {t s : Nat} (port : Fin t) (worker : Machine t s) := Composition.machine (retreat port) worker
def downMachine {t s : Nat} (port : Fin t) (worker : Machine t s) := RepeatMachine.machine (downBody port worker) (fun _ _=>true)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexedAt
