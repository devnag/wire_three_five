import Proof.MachineModel.NativeRound

/-! Canonical reusable states change only the source and append positions.
Every other ambient tape is the same actual initialized workspace. -/
namespace NearCubicWires.ExtIncidence.NativeState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def heads (H : Fin 277→ℕ) (pos : ℕ) (out : List Bool):=
  dockH bank H (extraH pos out)
noncomputable def tapes (A : Fin 277→List Bool) (data : Fin 15→List Bool)
    (C : ℕ) (source out : List Bool):=install bank A (word data C source out)

end NearCubicWires.ExtIncidence.NativeState
