import Proof.Packets.NativeMaskCount
import Proof.Packets.NormalizedAdditionData

/-! A native monomial stream is physically parsed into raw support masks,
counted, and returned to the ready operand layout. The source polynomial
and its row count are not supplied a second time as mask-bank advice. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryExecution

def masks (C : Nat) (P : List (List Nat)) := P.map (ExtIncidence.maskOf C)
def nativeSlots : Fin 5→Fin 32 := ![30,24,31,26,27]
def countSlots : Fin 1→Fin 32 := ![27]
def backSlots : Fin 4→Fin 32 := ![24,26,29,27]
noncomputable abbrev native := RecoveryFocus.machine nativeSlots NativeMaskCount.machine
noncomputable abbrev countReady := RecoveryFocus.machine countSlots PairCountReady.machine
noncomputable abbrev back := RecoveryFocus.machine backSlots MaskBack.machine
noncomputable abbrev prepare := Composition.machine native (Composition.machine countReady back)

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
