import Proof.CaseAnalysis.RowsSupportTermLayout
import Proof.CaseAnalysis.RowsSupportThresholdCircuit
import Proof.CaseAnalysis.WitnessFamilyMode

/-! The literal two circuit modes supply the same original verdict/native
semantics together with each kept gate's declared support frame. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyMode
open LocalBitMultitape CloseoutWitness CloseoutRowsCircuitTermSupplier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def program (sym : Bool):Σ s,Machine 1704 s:=
  if sym then ⟨Symmetric.program.1,Symmetric.machine⟩ else ⟨Threshold.program.1,Threshold.machine⟩
def machine (sym : Bool):Machine 1704 (program sym).1:=(program sym).2

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyMode
