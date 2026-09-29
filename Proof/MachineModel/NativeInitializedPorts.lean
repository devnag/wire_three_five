import Proof.MachineModel.NativeInitialize

/-! The initialized bank exposes exact native words, including the shared
measured driver, without any prepared native-input premise. -/
namespace NearCubicWires.ExtIncidence.NativeInitializedPorts
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout NativeInitialize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (data : Fin 15→List Bool) (C : ℕ) (source out : List Bool) (i : Fin 128):=
  if i=31 then out else if i=104 then List.replicate C true
  else if i=105 then List.replicate (C+1) false else if i=113 then source
  else ZeroPadding.pad C ((selection i.val).elim [] data)

end NearCubicWires.ExtIncidence.NativeInitializedPorts
