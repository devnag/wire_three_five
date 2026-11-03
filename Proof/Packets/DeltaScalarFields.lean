import Proof.Packets.DeltaSplitCounters
import Proof.Packets.ScalarSeedInto
import Proof.Packets.ScalarCounterInto
import Proof.Packets.ScalarTwiceInto

/-! Actual capped/offset counters and five framed delta metadata scalars from
retained numeric masters. All binary-zero frames are physically allocated;
no metadata frame enters the initial bank. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaScalarFields
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def splitSlots : Fin 5→Fin 25 := ![0,1,5,6,7]
def split := RecoveryFocus.machine splitSlots DeltaSplitCounters.returned

def seedOne (port : Fin 25) := ScalarSeedInto.zeroMachine port 13 4
def seed := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (seedOne 8) (seedOne 9)) (seedOne 10)) (seedOne 11)) (seedOne 12))
def cap := ScalarCounterInto.zeroMachine (8 : Fin 25) 13 5
def parentScalar := ScalarCounterInto.machine (9 : Fin 25) 13 2
def childScalar := ScalarCounterInto.machine (10 : Fin 25) 13 3
def offset := ScalarCounterInto.zeroMachine (11 : Fin 25) 13 6
def width := ScalarTwiceInto.zeroMachine (12 : Fin 25) 13 1
def convert := (Composition.machine (Composition.machine (Composition.machine (Composition.machine cap parentScalar) childScalar) offset) width)

def machine := Composition.machine split (Composition.machine seed convert)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaScalarFields
