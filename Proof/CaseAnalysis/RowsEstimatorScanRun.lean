import Proof.CaseAnalysis.RowsEstimatorScan

/-! The grouped scanner applied to the exact emitted cut bytes. The unary
cut count and byte count are outputs of this run, including the empty row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
open LocalBitMultitape RecoveryExecution Streaming MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countFields (row : EquationRow.Input):=2*row.d-row.odd.toNat+2

def ticks (row : EquationRow.Input):=
  (row.cuts.flatMap (cutWord row.p)).length+row.cuts.length*(2*countFields row+3)+2

def readyMachine:=Rewind.machine machine
def output (row : EquationRow.Input) : Fin 5→List Bool:=
  ![row.cuts.flatMap (cutWord row.p),UnaryTemplate.tape (countFields row),
    List.replicate row.cuts.length true,
    List.replicate (row.cuts.flatMap (cutWord row.p)).length true,
    List.replicate (ticks row) false]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
