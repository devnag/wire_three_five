import Proof.CaseAnalysis.CloseoutRowsEstimatorFields
import Proof.CaseAnalysis.RowsEstimatorHeader

/-! Cold row preparation. Raw d, p, parity and the actual cut bytes are
all inputs; both cut-count and byte-count words are physically produced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Prepare
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots : Fin 10→Fin 64:=![0,54,55,56,57,58,59,60,61,62]
def scanSlots : Fin 5→Fin 64:=![52,61,34,53,63]
def input (row : EquationRow.Input) (i : Fin 64):=
  if i=0 then List.replicate row.d true else if i=17 then List.replicate row.p true
  else if i=52 then Header.stream row else if i=54 then [row.odd] else []
noncomputable def middle (row : EquationRow.Input):=install fieldSlots (input row) (Fields.output row.d row.odd)
noncomputable def output (row : EquationRow.Input):=install scanSlots (middle row) (Scan.output row)
noncomputable def first:=RecoveryFocus.machine fieldSlots Fields.machine
noncomputable def last:=RecoveryFocus.machine scanSlots Scan.readyMachine
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input):=Fields.budget row.d row.odd+1+(2*Scan.ticks row+2)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Prepare
