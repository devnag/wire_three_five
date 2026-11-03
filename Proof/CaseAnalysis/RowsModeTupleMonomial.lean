import Proof.CaseAnalysis.RowsModeTupleLoop
import Proof.Supplier.RowTupleFrame

/-! One actual enumerated tuple frame emits exactly one raw monomial,
including its two monomial markers and the paid three-cell source trailer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : Nat) (out : List Bool) : Fin 7→Nat:=![pos,0,1,0,0,out.length,1]
def data (w k C : Nat) (source copy out : List Bool) : Fin 7→List Bool:=
  ![source,frame copy,CompareMachine.word w,[false],List.replicate C false,out,CompareMachine.word k]

def first : Machine 7 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun i=>if i=5 then some true else none,
    fun i=>if i=5 then .right else .stay⟩ else none
def last : Machine 7 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q _=>if h:q.val<3 then some ⟨⟨q.val+1,by omega⟩,
    fun i=>if q=0 ∧ i=5 then some false else none,
    fun i=>if i=0 ∨ (q=0 ∧ i=5) then .right else .stay⟩ else none
noncomputable def machine:=Composition.machine (Composition.machine first CloseoutRowsModeTupleLoop.machine) last

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleMonomial
