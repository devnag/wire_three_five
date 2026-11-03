import Proof.MachineModel.Runs
import Proof.MachineModel.UWalkUnary
import Proof.PCP.ProjectionDimensionTemplate
import Proof.PCP.ProjectionDimensionPower

/-! Produce the framed support-record width W=2B+3 from the actual measured
pool-count template. The fixed worker emits every scalar and returns with W's
cursor at its first unary mark, as required by the physical normalizer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleMaskWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairSource.ProjectionNormalization
noncomputable section

def worker1 := UWalkUnary.machine false false

def worker2 := DimensionTemplate.machine true

def worker3 := DimensionPower.machine 1 2

def worker4 := DimensionTemplate.machine true

-- BEGIN GENERATED

def slots1 : Fin 3→Fin 11 := ![0,1,2]
def phase1 := RecoveryFocus.machine slots1 worker1

def joined1 := phase1

def slots2 : Fin 3→Fin 11 := ![1,3,4]
def phase2 := RecoveryFocus.machine slots2 worker2

def joined2 := Composition.machine joined1 phase2

def slots3 : Fin 5→Fin 11 := ![3,5,6,7,8]
def phase3 := RecoveryFocus.machine slots3 worker3

def joined3 := Composition.machine joined2 phase3

def slots4 : Fin 3→Fin 11 := ![7,9,10]
def phase4 := RecoveryFocus.machine slots4 worker4

def joined4 := Composition.machine joined3 phase4

def raise : Machine 11 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=9 then .right else .stay⟩ else none

def machine := Composition.machine joined4 raise

end
end Theorem25Completion.CycleMaskWidth
