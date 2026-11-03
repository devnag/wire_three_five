import Proof.CaseAnalysis.RowsDegreeReset
import Proof.Amplification.RecoveryScratchErase

/-! The actual degree call's reset is followed by a paid coarse sweep.
The native row context and append cursor survive; all 57 degree-work tapes
and both recording tapes are ready for the next metadata load. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeClean
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsDegreeReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 59) : Fin 106 :=
  if i.val=0 then 44 else if i.val=1 then 47 else if i.val=2 then 48
  else if i.val<57 then ⟨i.val+46,by omega⟩ else ⟨i.val+47,by omega⟩

noncomputable def first {s : ℕ} (p : Machine 103 s) := TapeEmbedding.machine 2 (CloseoutRowsDegreeReset.machine p)
noncomputable def last := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 57)
noncomputable def machine {s : ℕ} (p : Machine 103 s) := Composition.machine (first p) last

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeClean
