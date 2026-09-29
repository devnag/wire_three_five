import Proof.CaseAnalysis.FinalWidthCopies
import Proof.CaseAnalysis.FinalTailComposeVerdict

/-! Paper C.10/C.10.1: one run computes the three estimates and their verdict.
The body below extends the existing three-block body by the six paid physical
width copies. The unchanged length gate then runs that body and the fixed tail.
Every width is the width of its own record, read from a retained block output. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths

open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairRepresentation CompetitorRationalGap
open C10TailCompose C10BodyWidths C10TailSlotsUniform
open C10TailVerdict (tailBank tailFlag tailSpare scratchT)
open C10TailUniformSlots (phaseIndex widthSlot privateSlot)
open C10TailFeedDockUniform (PhaseParked)
open C10TailVerdictUniform (ParkedThree' TailWidths' tbud)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def lengths (W : Phase → ℕ) (k : Fin 6) : ℕ :=
  if (C10WidthCopies.partOf k).val = 0 then W (C10WidthCopies.phaseOf k)
  else CompetitorRationalDecision.width (W (C10WidthCopies.phaseOf k))

variable (e : ℕ) (he : 58 ≤ e)

def bodyFuel (F W : Phase → ℕ) : ℕ := bodyThreeFuel F+1+C10WidthCopies.budget (lengths W)

def maxWidth (W : Phase → ℕ) : ℕ := max (W .penalty) (max (W .moment) (W .clause))

def innerFuel (F W : Phase → ℕ) (budget : ℕ → ℕ) : ℕ :=
  bodyFuel F W+1+(2*budget (maxWidth W)+2)

end
end NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths
