import Proof.Packets.UnaryAffine
import Proof.MachineModel.Runs
import Proof.MachineModel.UWalkUnary
import Proof.CaseAnalysis.CapacityPower

/-! A fixed 48-tape program physically generates the shared reset reserve
65536*(B+1)^4*2^(8*w) from the measured pool and chosen width templates.
The constant 65536 is generated as 2^16 by paid arithmetic. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleCommonReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairSource
open NearCubicWires.RepairSource.VerifierDecoding
open Completion
noncomputable section


def worker1 := UWalkUnary.machine false true

def worker2 := DimensionTemplate.machine false

def worker3 := DimensionPower.machine 4 1

def worker4 := UWalkUnary.machine false false

def worker5 := UnaryAffine.machine 8 16

def worker6 := CloseoutCapacity.Power.machine

def worker7 := ClockUnaryProduct.machine

def worker8 := DimensionTemplate.machine false

-- BEGIN GENERATED WIRING

def slots1 : Fin 3→Fin 48 := ![0,2,3]
def phase1 := RecoveryFocus.machine slots1 worker1

def joined1 := phase1

def slots2 : Fin 3→Fin 48 := ![2,4,5]
def phase2 := RecoveryFocus.machine slots2 worker2

def joined2 := Composition.machine joined1 phase2

def slots3 : Fin 11→Fin 48 := ![4,6,7,8,9,10,11,12,13,14,15]
def phase3 := RecoveryFocus.machine slots3 worker3

def joined3 := Composition.machine joined2 phase3

def slots4 : Fin 3→Fin 48 := ![1,16,17]
def phase4 := RecoveryFocus.machine slots4 worker4

def joined4 := Composition.machine joined3 phase4

def slots5 : Fin 11→Fin 48 := ![16,18,19,20,21,22,23,24,25,26,27]
def phase5 := RecoveryFocus.machine slots5 worker5

def joined5 := Composition.machine joined4 phase5

def slots6 : Fin 17→Fin 48 := ![26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43]
def phase6 := RecoveryFocus.machine slots6 worker6

def joined6 := Composition.machine joined5 phase6

def slots7 : Fin 4→Fin 48 := ![14,40,44,45]
def phase7 := RecoveryFocus.machine slots7 worker7

def joined7 := Composition.machine joined6 phase7

def slots8 : Fin 3→Fin 48 := ![44,46,47]
def phase8 := RecoveryFocus.machine slots8 worker8

def joined8 := Composition.machine joined7 phase8

abbrev machine := joined8

end
end Theorem25Completion.CycleCommonReserve
