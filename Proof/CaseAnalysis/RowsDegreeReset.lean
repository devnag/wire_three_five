import Proof.CaseAnalysis.RowsComputedCuts
import Proof.PCP.PCPSerializerTapeSupport

/-! The fixed-degree call executes one recorded rewind of its reusable
work tapes. Its append cursor is excluded. The coarse capacity concerns
only those work tapes, so accumulated row output never enters this charge. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeReset
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 103) : Bool := decide (i=44 ∨ i=47 ∨ i=48 ∨ 49 ≤ i.val)
def caps (C : ℕ) (i : Fin 103) := if selected i then C else 0

noncomputable def machine {s : ℕ} (p : Machine 103 s) := MaskedReset.machine p selected

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeReset
