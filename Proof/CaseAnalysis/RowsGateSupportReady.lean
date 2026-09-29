import Proof.CaseAnalysis.RowsGateSupportLoop

/-! The retained native weights, bitmap and actual weight-count word feed
the whole support pass directly. A paid bootstrap supplies its flag and
driver head, and a paid rewind restores every final physical head. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RecoveryExecution RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (fields : List (Bool×List Bool)) (membership : List Bool) : Fin 6→List Bool:=
  ![fields.flatMap fieldWord,[],[],frame membership,[],CompareMachine.word fields.length]
def bootstrap : Machine 6 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=4 then some true else none,fun i=>if i=5 then .right else .stay⟩ else none
noncomputable def preparedMachine (compressed : Bool):=Composition.machine bootstrap (loop compressed)
def preparedBudget (w count : ℕ):=loopBudget w count+2

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
