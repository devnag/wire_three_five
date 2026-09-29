import Proof.CaseAnalysis.WitnessFamilyBank

/-! The paid coefficient-width and original family-frame copies use the
already allocated banks. Only their two destination tapes change; the
logical streams and the actual source policy are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyReload
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def widthSlots : Fin 4 → Fin 3243 := ![3241,149,720,721]
def rawSlots : Fin 4 → Fin 3243 := ![3242,3064,2530,2531]
def widthCopy:=RecoveryFocus.machine widthSlots RecoveryBoundedTapeCopy.machine
def rawCopy:=RecoveryFocus.machine rawSlots RecoveryBoundedTapeCopy.machine
def copies:=Composition.machine widthCopy rawCopy

def prime : Machine 3243 2 where
  descriptionBits:=0
  start:=0
  halted:=fun state=>state.val==1
  rule:=fun state _=>if state.val=0 then
    some ⟨1,fun i=>if i=724 then some false else none,fun _=>.stay⟩ else none

def machine:=Composition.machine copies prime

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyReload
