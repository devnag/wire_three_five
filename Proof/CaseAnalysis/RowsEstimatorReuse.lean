import Proof.CaseAnalysis.CloseoutRowsEstimatorWarm
import Proof.CaseAnalysis.RowsEstimatorReuseRun
import Proof.CaseAnalysis.RowsEstimatorDriverBounds

/-! The same append/sweep bank after the scanner interposition. The warm
callee starts with every head zero, so the original complete rewind suffices;
no special native-cursor reset premise is needed. D backing is supplied by
the checked physical pad-in-place pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmReuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s):=
  TapeEmbedding.machine 2 (Rewind.machine worker)
noncomputable def machine {s : ℕ} (p : Program) (worker : Machine (WholePrefix.tapes p) s):=
  Composition.machine (first p worker) (Reuse.after p)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmReuse
