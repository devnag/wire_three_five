import Proof.CaseAnalysis.RowsRawRecord

/-! Projection contracts suffice for the paid reset/erase boundary. The
actual worker run, initial scratch support and physical drivers remain
premises. No final Williams/table-bank identity is required. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsProjectionReset
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scratch_support {t s : ℕ} (p : Machine t s) (fuel cap : ℕ)
    (c : Configuration t s) (source : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some source) (i : Fin t)
    (hh : c.heads i = 0) (ht : (c.tapes i).length ≤ cap)
    (hc : source.steps+1 ≤ cap) : (source.final.tapes i).length ≤ cap := by
  have h := PCPSerializerReuse.tape_support p fuel c source hr i cap 0
    (by omega) (ht.trans (Nat.le_max_left _ _))
  simpa only [zero_add,Nat.max_eq_left hc] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsProjectionReset
