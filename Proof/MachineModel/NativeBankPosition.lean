import Proof.MachineModel.NativeBankInputs

/-! One actual transition places the retained native loop headers while
leaving the source and growing output cursors in place. -/
namespace NearCubicWires.ExtIncidence.NativeBankPosition
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout NativeInitialize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions (i : Fin 277) : HeadMove:=if i=bank 15 ∨ i=bank 18 ∨ i=bank 24 ∨
    i=bank 35 ∨ i=bank 37 ∨ i=bank 38 ∨ i=bank 45 ∨ i=bank 46 ∨ i=bank 112 then .right else .stay
def machine:=DecompositionCountPosition.move directions

end NearCubicWires.ExtIncidence.NativeBankPosition
