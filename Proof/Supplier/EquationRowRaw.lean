import Proof.Supplier.EquationRowCuts
import Proof.Supplier.EquationRowPrepare

/-! Whole original-row to literal matrix-request byte production. Every
header, loop driver, scratch buffer and two-cut output is physically made. -/
namespace NearCubicWires.RepairOrdinary.EquationRowRaw
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 22 → Fin 126 := ![1,111,112,113,114,115,116,117,118,119,120,121,122,123,110,60,125,34,38,33,124,40]
noncomputable def last := RecoveryFocus.machine slots EquationRowCuts.machine
noncomputable def machine := Composition.machine EquationRowPrepare.machine last
def source (r : EquationRow.Input) := EquationHeaderRead.word r.d r.p r.cuts.length
  (r.odd::EquationRowCuts.stream r.p r.cuts)


end NearCubicWires.RepairOrdinary.EquationRowRaw
