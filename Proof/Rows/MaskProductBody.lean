import Proof.Rows.MaskProductInner
import Proof.Rows.MaskProductBack
import Proof.Rows.PhysicalFocusBoundary

/-! One complete outer iteration: emit the right-minor products, restore
its right-bank cursor by counted traversal, then advance the left cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def backSlots : Fin 4→Fin 6 := ![0,2,3,5]
noncomputable def seekSlots : Fin 3→Fin 6 := ![0,1,3]
noncomputable def body := Composition.machine inner
  (Composition.machine (RecoveryFocus.machine backSlots MaskBack.machine)
    (RecoveryFocus.machine seekSlots MaskSeek.body))


end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
