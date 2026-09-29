import Proof.CaseAnalysis.RowsEstimatorWhole

/-! Stop the mandatory cold prefix at its existing exact scanner boundary.
Raw d, p, G and literal byte count are available before the reset capacity
is evaluated. No second source scan or guessed count is introduced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scanned
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (C : ℕ) : Fin 6→List Bool:=![[],[],[],[],List.replicate C true,List.replicate C false]
noncomputable def output (row : EquationRow.Input) (C : ℕ) : Fin 70→List Bool :=
  Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) (Prepare.output row) (extra C)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scanned
