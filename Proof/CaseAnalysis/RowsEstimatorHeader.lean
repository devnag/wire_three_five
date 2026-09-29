import Proof.CaseAnalysis.RowsEstimatorTail

/-! The scanner's two actual unary outputs feed the existing three-header
printer and the literal parity/cut append. The same checked outer framer
then supplies EquationRowRaw's original source codec. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Header
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (row : EquationRow.Input) : Fin 3→ℕ:=![row.d,row.p,row.cuts.length]
def stream (row : EquationRow.Input):=row.cuts.flatMap (cutWord row.p)
def slots : Fin 4→Fin 55:=![52,53,54,51]
noncomputable def first:=TapeEmbedding.machine 3 EquationHeaders.machine
noncomputable def last:=RecoveryFocus.machine slots Tail.machine
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input):=EquationHeaders.budget (values row)+1+(stream row).length+2

noncomputable def framed:=AppendOutputFrame.machine machine 51
def framedBudget (row : EquationRow.Input):=6*budget row+7

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Header
