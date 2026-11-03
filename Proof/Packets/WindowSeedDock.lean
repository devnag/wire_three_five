import Proof.Packets.WindowSeedScalar
import Proof.Rows.PhysicalFocusBoundary

/-! The actual seed workers overwrite only their named destination in the
69-tape window/metadata arena. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def copySlots (s d : Fin 69) : Fin 4→Fin 69 := ![s,d,50,51]
def rawSlots (s d : Fin 69) : Fin 3→Fin 69 := ![s,d,51]
def valueSlots (s d : Fin 69) : Fin 3→Fin 69 := ![d,51,s]
def copyAt (s d : Fin 69) := RecoveryFocus.machine (copySlots s d) copy
def rawAt (s d : Fin 69) := RecoveryFocus.machine (rawSlots s d) raw
def zeroAt (s d : Fin 69) := RecoveryFocus.machine (rawSlots s d) scalarZero
def valueAt (s d : Fin 69) := RecoveryFocus.machine (valueSlots s d) scalarValue
def predAt (d : Fin 69) := RecoveryFocus.machine (fun _ : Fin 1=>d) countPred

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
