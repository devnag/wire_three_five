import Proof.Supplier.RowTupleMaskLoop

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


end NearCubicWires.RepairOrdinary.RowTupleCommonEquation
