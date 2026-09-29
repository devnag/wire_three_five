import Proof.MachineModel.NativeFanoutLayout

/-! One whole ordinary run measures the actual cache, produces every static
word and C, then physically initializes the native bank. -/
namespace NearCubicWires.ExtIncidence.NativeInitialize
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraH (pos : ℕ) (out : List Bool) (i : Fin 128):=
  if i=31 then out.length else if i=113 then pos else 0

end NearCubicWires.ExtIncidence.NativeInitialize
