import Proof.Packets.PacketsXLiteralPair
import Proof.CaseAnalysis.RowsCountBinary
import Proof.MachineModel.UWalkUnary

/-! Paid unary metadata to exact native literal-pair cache record. No binary
index, normalized pair operand, or completed result is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairUnary
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.RepairOrdinary.SignedSortKey
noncomputable section

def worker1 := UWalkUnary.machine false false

def worker2 := CloseoutRowsCountBinary.machine

def worker3 := UWalkUnary.machine false false

def worker4 := CloseoutRowsCountBinary.machine

def worker5 := LiteralPairCold.machine

-- BEGIN GENERATED WIRING

def slots1 : Fin 3→Fin 58 := ![0,3,4]
def phase1 := RecoveryFocus.machine slots1 worker1

def joined1 := phase1

def slots2 : Fin 10→Fin 58 := ![3,5,6,7,8,9,10,11,12,13]
def phase2 := RecoveryFocus.machine slots2 worker2

def joined2 := Composition.machine joined1 phase2

def slots3 : Fin 3→Fin 58 := ![1,14,15]
def phase3 := RecoveryFocus.machine slots3 worker3

def joined3 := Composition.machine joined2 phase3

def slots4 : Fin 10→Fin 58 := ![14,16,17,18,19,20,21,22,23,24]
def phase4 := RecoveryFocus.machine slots4 worker4

def joined4 := Composition.machine joined3 phase4

def slots5 : Fin 36→Fin 58 := ![25,26,9,20,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,2]
def phase5 := RecoveryFocus.machine slots5 worker5

def joined5 := Composition.machine joined4 phase5

abbrev machine := joined5

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairUnary
