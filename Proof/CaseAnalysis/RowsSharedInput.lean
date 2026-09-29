import Proof.CaseAnalysis.RowsSharedDigits

/-! The shared digit-width family inhabits the literal row input and
count-table premises. The cache width, single successor widening, scalar
width and complete matrix dimensions are inherited without alteration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSharedInput
open MatrixScoreBatch CloseoutRowsCacheInput CloseoutRowsSharedDigits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w) : EquationRow.Input :=
  let base := CloseoutRowsCacheInput.input s Q gs bank hs hg
  let hp := (batch_perm gs Q w bank hw).trans
    (CloseoutRows.ordered_batch_perm (RowCachedCoordinateBounds.width gs) Q (family gs bank)).symm
  { d:=base.d, p:=base.p, odd:=base.odd, cuts:=bank.flatMap (cuts gs Q w)
    lengths:=fun c hc=>base.lengths c (hp.mem_iff.mp hc)
    fits:=fun c hc=>base.fits c (hp.mem_iff.mp hc)
    oddPositive:=base.oddPositive
    gateSquare:=by rw [hp.length_eq]; exact base.gateSquare }

end NearCubicWires.RepairOrdinary.CloseoutRowsSharedInput
