import Proof.CaseAnalysis.WitnessSumRound

/-! Each accepted outer-family field is loaded once into the shared sum
bank. Its verdict cell is then reset in one real step before the sum
header starts; previous logical output prefixes are never traversed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 3063 := ![3061,2534,3062]
noncomputable def loader:=RecoveryFocus.machine slots FrameLoad.machine

def prime : Machine 3063 2 where
  descriptionBits:=0
  start:=0
  halted:=fun state=>state.val==1
  rule:=fun state _=>if state.val=0 then
    some ⟨1,fun i=>if i=724 then some false else none,fun _=>.stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
