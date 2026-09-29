import Proof.CaseAnalysis.PairClockExact
import Proof.CaseAnalysis.ScheduleCompare
import Proof.CaseAnalysis.WitnessSelectedStreamsLayout

/-! Exact oracle-size acceptance on the produced raw arity and size.
The checked pairing-clock identity reuses the existing power producer and
size+1 template, with no decrement, serialization or enlarged cap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace Core
abbrev P (D : ℕ):=DimensionPolynomial.tapes D
abbrev tapes (D : ℕ):=P D+6
def qSlot (D : ℕ) : Fin (tapes D):=⟨0,by dsimp [tapes,P,DimensionPolynomial.tapes];omega⟩
def sizeSlot (D : ℕ) : Fin (tapes D):=⟨1,by dsimp [tapes,P,DimensionPolynomial.tapes];omega⟩
def powerSlots (D : ℕ) (i : Fin (P D)) : Fin (tapes D):=
  if i.val=0 then qSlot D else ⟨2+i.val,by dsimp only [tapes]; omega⟩
def templateSlots (D : ℕ) : Fin 3→Fin (tapes D):=
  ![sizeSlot D,⟨P D+2,by dsimp only [tapes]; omega⟩,⟨P D+3,by dsimp only [tapes]; omega⟩]
def compareSlots (D : ℕ) : Fin 4→Fin (tapes D):=
  ![⟨P D+2,by dsimp only [tapes]; omega⟩,powerSlots D (DimensionPolynomial.rawSlot D),
    ⟨P D+4,by dsimp only [tapes]; omega⟩,⟨P D+5,by dsimp only [tapes]; omega⟩]
def flagSlot (D : ℕ):=compareSlots D 2


def power (D : ℕ):=RecoveryFocus.machine (powerSlots D) (DimensionPolynomial.machine D 1)
def template (D : ℕ):=RecoveryFocus.machine (templateSlots D) (DimensionTemplate.machine true)
def compare (D : ℕ):=RecoveryFocus.machine (compareSlots D) MatrixBucketDimensions.Compare.machine
def machine (D : ℕ):=Composition.machine (Composition.machine (power D) (template D)) (compare D)

end Core

def degree (G : ℕ):=2^(RecoveryScheduleEnvelope.oracleDepth G)
def machine (G : ℕ):=Core.machine (degree G)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap
