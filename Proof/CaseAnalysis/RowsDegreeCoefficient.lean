import Proof.CaseAnalysis.RowsDegreeSign
import Proof.Hierarchy.CompetitorDenominator

/-! The actual binLift coefficient is computed once from unary j and the
common unary width p. Existing power, normalization and signed-field writers
produce its complete cached frame in linear short-width time. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeCoefficient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CloseoutRowsDegreeSign (positive)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signSlots : Fin 3 → Fin 14 := ![0,2,3]
def powerSlots : Fin 6 → Fin 14 := ![0,4,5,6,7,8]
def normalizeSlots : Fin 5 → Fin 14 := ![1,4,9,10,11]
def emitSlots : Fin 4 → Fin 14 := ![2,9,12,13]
noncomputable def sign := RecoveryFocus.machine signSlots CloseoutRowsDegreeSign.machine
noncomputable def power := RecoveryFocus.machine powerSlots ClockFields.machine
noncomputable def normalize := RecoveryFocus.machine normalizeSlots ClockNormalize.machine
noncomputable def emit := RecoveryFocus.machine emitSlots RowCoefficientEmit.machine
noncomputable def machine := Composition.machine sign
  (Composition.machine power (Composition.machine normalize emit))

def input (j p : ℕ) : Fin 14 → List Bool :=
  ![List.replicate j true,List.replicate p true,[],[],[],[],[],[],[],[],[],[],[],[]]

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeCoefficient
