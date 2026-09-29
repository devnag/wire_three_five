import Proof.CaseAnalysis.FinalDecidesBridgeUniform
import Proof.CaseAnalysis.FinalStageSeamBlock

/-! Paper C.10 uses the three estimated means at one run. The decision tail
needs the width of each phase's actual record, so the retained width words
must survive the three blocks on their physical tapes. This strengthens the
existing body run only by those six outputs and the prefix scratch frame.
The body machine and its paid budget are unchanged. Tapes 274/275 are the
retained outputs fixed by external_in.md section 0.2; no width is an input oracle. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths

open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open C10TailCompose
open CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (e : ℕ) (he : 58 ≤ e)

def retained (j : Fin 2) : Fin (218+e) := ⟨274+j.val, by omega⟩
@[simp] theorem retained_val (j : Fin 2) : (retained e he j).val = 274+j.val := rfl

def widthWord (b : ℕ) (j : Fin 2) : List Bool :=
  List.replicate (if j.val = 0 then b else CompetitorRationalDecision.width b) true


end
end NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
