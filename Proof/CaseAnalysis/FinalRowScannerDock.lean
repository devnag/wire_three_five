import Proof.CaseAnalysis.FinalRowScannerReload
import Proof.CaseAnalysis.FinalRowFrameJoin

/-! The scanner reload at the actual post-row bank. The native header has
already been overwritten by its paid producer. Only the three named source
fields are added; the existing D driver/log and all other tapes are retained. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerDock
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def small (p : Program) (i : Fin 64) : Fin (Reuse.tapes p + 3) :=
  ⟨i.val, by have h := tapes_ge p; have hi := i.isLt; unfold Reuse.tapes; omega⟩
def slots (p : Program) : Fin 69 → Fin (Reuse.tapes p + 3) :=
  Fin.addCases (m:=64) (n:=5) (motive:=fun _ => Fin (Reuse.tapes p + 3)) (small p)
    ![(0 : Fin 3).natAdd (Reuse.tapes p), (1 : Fin 3).natAdd (Reuse.tapes p),
      (2 : Fin 3).natAdd (Reuse.tapes p), (Reuse.driver p).castAdd 3, (Reuse.log p).castAdd 3]


end NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerDock
