import Proof.CaseAnalysis.RowsIntegerFlag
import Proof.CaseAnalysis.WitnessMassReset
import Proof.CaseAnalysis.WitnessSumCheck

/-! Preserve the exact mass verdict before resetting the accumulator. The
same source and coefficient stream survive both reusable-bank resets. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumFinish
open LocalBitMultitape RecoveryRootRound CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 94) : Fin 827:=((i.castAdd 7).natAdd 725).castAdd 1
def flagSlots : Fin 2→Fin 827:=![790,724]
noncomputable def foldFlag:=RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
noncomputable def reset:=RecoveryFocus.machine nativeSlots bootstrapProgram
noncomputable def checked (k : ℕ) (q : ℚ):=Composition.machine (SumCheck.machine k q) foldFlag
noncomputable def cleared (k : ℕ) (q : ℚ):=Composition.machine (checked k q) reset
noncomputable def machine (k : ℕ) (q : ℚ):=Composition.machine (cleared k q) TermCommit.erase


end NearCubicWires.RepairOrdinary.CloseoutWitness.SumFinish
