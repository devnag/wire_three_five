import Proof.CaseAnalysis.RowsDegreeAdvance

/-! Between degree calls, physically reset the retained lookup bound and
advance both k templates and j. All native row heads, including the output
append cursor, survive. Only four existing small routines are composed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeNext
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameSlots : Fin 4→Fin 112 := ![39,40,103,105]
def nativeSlots : Fin 1→Fin 112 := fun _=>46
def templateSlots : Fin 1→Fin 112 := fun _=>108
def rawSlots : Fin 2→Fin 112 := ![110,103]
noncomputable def frameProgram := RecoveryFocus.machine frameSlots copyMachine
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlots RecoveryEraseWidth.incrementMachine
noncomputable def templateProgram := RecoveryFocus.machine templateSlots CloseoutRowsDegreeAdvance.templateMachine
noncomputable def rawProgram := RecoveryFocus.machine rawSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def first := Composition.machine frameProgram nativeProgram
noncomputable def second := Composition.machine first templateProgram
noncomputable def machine := Composition.machine second rawProgram


end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeNext
