import Proof.CaseAnalysis.RowsRawMonomialCopy

/-! Multiplication reuses the SAME left monomial without a copied cache.
The existing selective rewind returns its arbitrary starting cursor because
the actual body copier advances that cursor exactly once per instruction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialReturn
open LocalBitMultitape CloseoutRowsRawMonomialCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=SelectiveReset.machine CloseoutRowsRawMonomialCopy.machine 0

end NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialReturn
