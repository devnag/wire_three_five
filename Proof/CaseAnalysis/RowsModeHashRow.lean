import Proof.CaseAnalysis.RowsModeHashPrepare

/-! One complete physical hash row returns its scans, appends the computed
bit, and positions the original seed for the next row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashRow
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsModeHashReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def append : Machine 9 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bits=>if q=0 then some ⟨1,fun i=>if i=8 then some (bits 6) else none,
    fun i=>if i=8 then .right else .stay⟩ else none
noncomputable def first:=Composition.machine (TapeEmbedding.machine 1 CloseoutRowsModeHashReturned.machine) append
noncomputable def machine:=Composition.machine first (TapeEmbedding.machine 1 CloseoutRowsModeHashPrepare.machine)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashRow
