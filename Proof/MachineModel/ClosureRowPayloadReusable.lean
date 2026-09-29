import Proof.MachineModel.ClosureRowPayload

/-! The raw count reader returns a zeroed, bounded record buffer and a reusable
log, retaining the raw stream's append cursor. No literal-blank restoration
is requested. This is the output adapter for the external-row body.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RowPayloadReusable
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsEstimatorCoefficients SignedSortKey

def keep : Fin 2 → Bool := ![true,false]
noncomputable def first := TapeEmbedding.machine 1 (MaskedReset.machine RowPayload.machine keep)
def eraseSlots : Fin 3 → Fin 4 := ![0,3,2]
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine first last
def budget (b B : Nat) := 2*RowPayload.budget b+2+1+(2*B+4)


end NearCubicWires.P1Closure.RowPayloadReusable
