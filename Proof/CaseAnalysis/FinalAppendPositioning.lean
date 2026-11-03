import Proof.CaseAnalysis.FinalSiteRoundPortAppend
import Proof.PCP.PCPPQueryRows
import Proof.Circuits.DecompositionCountPosition

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AppendPositioning

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seekSlots : Fin 4 → Fin 5 := ![4, 1, 2, 3]

def data (width : ℕ) (payload out : List Bool) (logSize count : ℕ) : Fin 5 → List Bool :=
  ![payload, out, List.replicate logSize false, CompareMachine.word count,
    UnaryTemplate.tape (20 * width + 22)]

def enter := DecompositionCountPosition.move
  (![.stay, .stay, .stay, .right, .right] : Fin 5 → HeadMove)
noncomputable def seek := RecoveryFocus.machine seekSlots PCPPQueryRows.skip

def seekBudget (width count : ℕ) := count * (2 * (20 * width + 22) + 7) + 3
def rawBudget (width count : ℕ) := 1 + 1 + seekBudget width count + 1 + CloseoutFinalC10SiteRoundPortAppend.twiceBudget width count
def budget (width count : ℕ) := 2 * rawBudget width count + 2

def tapes (width padding logSize resetSize : ℕ) (entry : Stream.Entry)
    (xs : List Stream.Entry) : Fin 6 → List Bool :=
  fun i => Fin.addCases (motive := fun _ => List Bool)
    (data width (ZeroPadding.pad padding (Stream.entryWord width entry))
      (Stream.words width xs) logSize xs.length) (fun _ : Fin 1 => List.replicate resetSize false) i


end NearCubicWires.RepairOrdinary.CloseoutFinalC10AppendPositioning
