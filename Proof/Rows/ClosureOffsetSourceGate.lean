import Proof.Rows.ClosureReusable48
import Proof.Rows.ClosureConstantGate

/-! Direct ordinary evaluation of one native strict threshold gate on one
physical assignment. The two signed scores and target adjustment are read
and computed, then compared; no table printer or ready gate answer is input. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetSourceGate
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsPoolWeight SignedSortKey

def compareSlots : Fin 4→Fin 44 := ![13,14,21,22]
def frameSlots : Fin 3→Fin 44 := ![21,23,24]
def appendSlots : Fin 4→Fin 44 := ![23,25,26,34]
noncomputable def paired := Composition.machine C10NaturalHardwireScoreInputs.machine
  (TapeEmbedding.machine 23 C10NaturalHardwireTarget.pairMachine)
noncomputable def compare := RecoveryFocus.machine compareSlots compareMachine
noncomputable def invert := RecoveryFocus.machine frameSlots RecoveryLiteralSignFrame.machine
noncomputable def append := RecoveryFocus.machine appendSlots CloseoutRowsSignedAppend.sign
noncomputable def core := Composition.machine (Composition.machine (Composition.machine paired compare) invert) append

end NearCubicWires.P1Closure.OffsetSourceGate
