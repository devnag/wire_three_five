import Proof.CaseAnalysis.RowsModeElementaryMasterPadding

/-! A two-transition selector reads the actual coefficient, original M,
and elementary degree. It preserves the constant monomial when M=a=0. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowSelect
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def result (guard live positiveDegree : Bool) : Fin 5:=
  if !guard then 2 else if live then 3 else if !positiveDegree then 4 else 2
def machine : Machine 60 5 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (2≤q.val)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=48 then .right else .stay⟩
    else if q=1 then some ⟨result (bits 56) (bits 59) (bits 48),fun _=>none,
      fun i=>if i=48 then .left else .stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowSelect
