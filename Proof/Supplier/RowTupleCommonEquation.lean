import Proof.Supplier.RowCommonCoordinateLoop
import Proof.Supplier.RowTupleMaskReady

/-! A whole selected tuple now reaches the complete common-width equation
emitter through shared physical occurrence/count tapes. The ordered native
positions come from executed cache lookups, including all repetitions. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCommonEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def one (N : ℕ) (bits : List Bool) : List (Fin N) :=
  if h : bits.length≤N then RowMaskMeaning.typed N 0 bits (by omega) else []

def tupleSlots : Fin 14→Fin 48 := ![36,37,23,24,38,39,40,41,42,43,44,45,46,47]
def rowSlots (i : Fin 36) : Fin 48 := i.castAdd 12
noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleMaskReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowTupleCommonEquation
